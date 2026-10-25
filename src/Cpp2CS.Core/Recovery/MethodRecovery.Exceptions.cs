using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private ExceptionLayout? exceptionLayout;
        private readonly Dictionary<ExceptionRegionPlan, LocalValue> caughtExceptions = [];
        private readonly Dictionary<Variable, LocalValue> exceptionValues = [];
        private readonly Dictionary<Variable, LocalValue> wrappers = [];
        private readonly Dictionary<Call, TypeRef> exceptionTypeTargets = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Variable, Phi> exceptionPhis = [];
        private readonly HashSet<Variable> exceptionDemand = [];
        private bool collectingExceptionDemand;
        private static ulong FragmentLabel(ExceptionFragment fragment) => 0xf500000000000000UL + (uint)fragment.Id;

        private bool PrepareExceptionRegions()
        {
            exceptionLayout = ExceptionRegionBuilder.Build(facts, function);
            if (!exceptionLayout.Succeeded) return false;
            var catchEntries = new Dictionary<ExceptionRegionPlan, Call>();
            foreach (var region in exceptionLayout.Regions.Where(r => r.Kind == "catch"))
            {
                var entries = region.Handler.SelectMany(f => f.Statements).OfType<Call>().Where(c => c.Op?.Kind == OpKind.BeginCatch).ToArray();
                if (entries is not [var begin])
                {
                    exceptionLayout = exceptionLayout with { Reason = "catch 入口未证明", Detail = $"BeginCatch 数量 {entries.Length}" };
                    return false;
                }
                catchEntries.Add(region, begin);
            }
            var incoming = new Dictionary<Block, HashSet<int>>();
            void KeepEdge(Block from, Block to, bool exceptional)
            {
                if (from == to) return;
                var successor = exceptional ? from.Successors.FindLastIndex(b => b == to) : from.NormalSuccessors.ToList().IndexOf(to);
                if (successor < 0) return;
                if (!incoming.TryGetValue(to, out var indices)) incoming[to] = indices = [];
                indices.Add(MachineFunction.PredecessorIndex(from, successor));
            }
            var fragments = exceptionLayout.Graph.Fragments.ToDictionary(f => f.Id);
            foreach (var edge in exceptionLayout.Edges.Where(e => e[2] == 0)) KeepEdge(fragments[edge[0]].Block, fragments[edge[1]].Block, false);
            foreach (var path in exceptionLayout.EntryPaths)
            {
                var from = path.Source.Block;
                foreach (var part in path.Bridges.Append(path.Entry)) { KeepEdge(from, part.Block, true); from = part.Block; }
            }
            // 类型推断只读已保留的入边；真正复制仍读取原图完整 phi 及原始前驱索引。
            foreach (var (block, indices) in incoming)
                foreach (var phi in block.Statements.OfType<Phi>())
                    exceptionPhis[phi.Target] = phi with { Sources = indices.Order().Select(i => phi.Sources[i]).ToArray() };
            var kept = exceptionLayout.Kept.Concat(exceptionLayout.EntryPaths.SelectMany(p => p.Bridges)).Select(f => f.Block).ToHashSet();
            blocks = function.Blocks.Where(kept.Contains).ToArray();
            foreach (var region in exceptionLayout.Regions.Where(r => r.Kind == "catch"))
            {
                var exception = StructLocal(types.Corlib("System.Exception"), 64);
                caughtExceptions.Add(region, exception);
                exceptionValues[exception.Variable] = exception;
                known[exception.Variable] = exception.Type;
                var begin = catchEntries[region];
                foreach (var variable in begin.Defines.OfType<Variable>()) wrappers[variable] = exception;
            }
            return true;
        }

        [Analysis("异常值", 10)]
        private void AnalyzeExceptionValues()
        {
            if (exceptionLayout is not { Succeeded: true }) return;
            foreach (var (variable, expression) in values)
                if (expression is Intrinsic { Name: "eh_exception" or "eh_selector" }) runtime.Add(variable);
            foreach (var variable in wrappers.Keys) runtime.Add(variable);
            var (closedWrappers, closedExceptions) = ExceptionValueClosure.Close(new MethodView(blocks, exceptionPhis).Statements, wrappers, exceptionValues);
            foreach (var (variable, wrapper) in closedWrappers) wrappers.TryAdd(variable, wrapper);
            foreach (var (variable, exception) in closedExceptions) exceptionValues.TryAdd(variable, exception);
            foreach (var variable in wrappers.Keys) runtime.Add(variable);
            foreach (var (variable, exception) in exceptionValues) known[variable] = exception.Type;
        }

        private bool PrepareExceptionTypeChecks()
        {
            if (exceptionLayout is not { Succeeded: true }) return false;
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
                if (call is { Op.Kind: OpKind.IsAssignableFrom, Arguments: [var target, Use klass] }
                    && Expand(target) is Symbol { Kind: SymbolKind.Class, Value: TypeRef type }
                    && values.TryGetValue(klass.Variable, out var value) && value is Load { Width: 64, Address: Use obj }
                    && exceptionValues.ContainsKey(obj.Variable))
                {
                    // E1 wrapper+0 已证明为非空托管异常；运行时类检查等价于对同一对象 isinst 后与 null 比较。
                    objectClasses[klass.Variable] = obj;
                    typeChecks[call] = obj;
                    exceptionTypeTargets[call] = type;
                    runtime.Add(klass.Variable);
                }
            return exceptionTypeTargets.Count != 0;
        }

        private ManagedBody BuildExceptionBody()
        {
            var layout = exceptionLayout!;
            var byId = layout.Graph.Fragments.ToDictionary(f => f.Id);
            var normal = layout.Edges.Where(e => e[2] == 0).GroupBy(e => e[0]).ToDictionary(g => g.Key, g => g.Select(e => byId[e[1]]).ToArray());
            // 只有 C++ 簿记的 cleanup 没有 CIL 入口，不把其 Resume 误写成普通可达代码。
            var active = new HashSet<ExceptionFragment>();
            var pending = new Stack<ExceptionFragment>(layout.Regions.Select(r => r.Entry).Prepend(layout.Graph.Entry));
            while (pending.TryPop(out var reached))
                if (active.Add(reached)) foreach (var next in normal.GetValueOrDefault(reached.Id) ?? []) pending.Push(next);
            var order = layout.Order.Where(active.Contains).ToArray();
            // selector 剪枝后，原图还可能保留只给外来路径或原生调用临时寄存器使用的 phi。
            // 从实际托管语句的读取回溯 SSA；有访存的定义仍是根，不能把可能抛出的加载当死代码删除。
            collectingExceptionDemand = true;
            foreach (var fragment in order)
                foreach (var statement in fragment.Statements)
                {
                    if (dropped.Contains(statement) || statement is Phi or Nop or Jump
                        or Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch or OpKind.ResumeUnwind }) continue;
                    if (statement is Define define)
                    {
                        if (runtime.Contains(define.Target) || exceptionValues.ContainsKey(define.Target)
                            || !ExprMap.Walk(define.Value).Any(e => e is Load)) continue;
                        exceptionDemand.Add(define.Target);
                    }
                    try
                    {
                        if (statement is Branch branch)
                        {
                            if ((normal.GetValueOrDefault(fragment.Id) ?? []).Length == 2) _ = Recover(branch.Condition, types.Boolean);
                        }
                        else
                        {
                            var translated = new List<ManagedStatement>();
                            Translate(fragment.Block, statement, translated);
                            // 帧拷贝等规则缓存了已恢复的值，不再经过 Variable；其读取也必须保留原生定义。
                            foreach (var value in translated.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                                .SelectMany(ManagedValues.Walk).OfType<LocalValue>()) exceptionDemand.Add(value.Variable);
                        }
                    }
                    catch (HoleException) { /* 实际写出遍历仍会记录这个洞；这里只收集已读到的来源。 */ }
                }
            collectingExceptionDemand = false;
            var work = new Queue<Variable>(exceptionDemand);
            while (work.TryDequeue(out var variable))
            {
                var sources = values.TryGetValue(variable, out var value) ? ExprMap.Walk(value).OfType<Use>().Select(u => u.Variable)
                    : phis.TryGetValue(variable, out var phi) ? phi.Sources : [];
                foreach (var source in sources) if (exceptionDemand.Add(source)) work.Enqueue(source);
            }
            var output = new List<ManagedBlock>();
            foreach (var fragment in order)
            {
                var statements = new List<ManagedStatement>();
                try
                {
                    foreach (var path in layout.EntryPaths.Where(p => p.Source == fragment && active.Contains(p.Entry))) ExceptionCopies(path, statements);
                    var successors = normal.GetValueOrDefault(fragment.Id) ?? [];
                    foreach (var statement in fragment.Statements)
                    {
                        if (dropped.Contains(statement)) continue;
                        if (statement is Define d && (runtime.Contains(d.Target) || exceptionValues.ContainsKey(d.Target) || !exceptionDemand.Contains(d.Target))) continue;
                        if (statement is Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch }) continue;
                        if (statement is Call { Op.Kind: OpKind.ResumeUnwind } resume)
                        {
                            if (!layout.Regions.Any(r => r.Kind == "fault" && r.Handler.Contains(fragment)))
                                throw Fail(resume.Address, "异常区域 可达清理未映射为 fault");
                            statements.Add(new ManagedEndFault(resume.Address)); continue;
                        }
                        if (statement is Branch branch)
                        {
                            if (successors is [var only]) statements.Add(new ManagedJump(branch.Address, ExceptionEdge(fragment, only)));
                            else if (successors.Length == 2) statements.Add(new ManagedBranch(branch.Address, Truth(Recover(branch.Condition, types.Boolean)),
                                ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Target)),
                                ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Fallthrough))));
                            else throw Fail(branch.Address, "异常区域 分支后继未证成");
                            continue;
                        }
                        if (statement is Jump jump)
                        {
                            if (successors is not [var only]) throw Fail(jump.Address, "异常区域 跳转后继未证成");
                            statements.Add(new ManagedJump(jump.Address, ExceptionEdge(fragment, only))); continue;
                        }
                        if (statement is IndirectJump table && switchIndices.TryGetValue(table, out var index))
                        {
                            var targets = successors.ToDictionary(f => f.Block.Start);
                            if (table.Targets.Any(t => !targets.ContainsKey(t))) throw Fail(table.Address, "异常区域 switch 后继未证成");
                            statements.Add(new ManagedSwitch(table.Address, Index(index),
                                table.Targets.Select(t => ExceptionEdge(fragment, targets[t])).ToArray()));
                            continue;
                        }
                        if (statement is Call { Op.Kind: OpKind.ThrowManaged or OpKind.Rethrow, Arguments: [Use value] } rethrow
                            && exceptionValues.TryGetValue(value.Variable, out var current)
                            // rethrow 指向最内层活动 catch；内层 catch 中再次抛出外层保存对象必须用 throw。
                            && caughtExceptions.Where(p => p.Key.Handler.Contains(fragment)).OrderBy(p => p.Key.Handler.Count).FirstOrDefault().Value == current)
                        { statements.Add(new ManagedRethrow(rethrow.Address)); continue; }
                        if (ledger.TryGetDiagnosis(statement, out var cause)) throw Derived(cause, "异常区域 语句已诊断");
                        Translate(fragment.Block, statement, statements);
                    }
                    if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedRethrow or ManagedEndFault or ManagedCall { Tail: true }))
                    {
                        if (successors is [var only]) statements.Add(new ManagedJump(fragment.Block.End, ExceptionEdge(fragment, only)));
                        else throw Fail(fragment.Block.Start, "异常区域 片段缺少终结方式");
                    }
                }
                catch (HoleException e) { Record(e, fragment.Block.Start); statements.Add(new ManagedHole(e.Address == 0 ? fragment.Block.Start : e.Address, e.Message, true)); }
                output.Add(new(FragmentLabel(fragment), statements));
            }
            return new ManagedBody(method, output)
            {
                Regions = layout.Regions.OrderByDescending(r => r.Try.Count + r.Handler.Count).Select(r => new ManagedRegion(
                    order.Where(r.Try.Contains).Select(FragmentLabel).ToArray(), FragmentLabel(r.Entry),
                    order.Where(r.Handler.Contains).Select(FragmentLabel).ToArray(), caughtExceptions.GetValueOrDefault(r),
                    r.Kind == "catch" ? ManagedRegionKind.Catch : ManagedRegionKind.Fault)).ToArray(),
            };
        }

        private ManagedEdge ExceptionEdge(ExceptionFragment from, ExceptionFragment to)
        {
            if (from.Block == to.Block) return new(FragmentLabel(to), []);
            var successor = from.Block.NormalSuccessors.ToList().IndexOf(to.Block);
            if (successor < 0) throw Fail(from.Block.Start, "异常区域 普通边没有原始 SSA 来源");
            return Edge(from.Block, successor, to.Block.Start) with { Target = FragmentLabel(to) };
        }

        /// <summary>
        /// 异常边的 phi 在可能抛出前快照。空桥逐级代入来源；普通边索引只用于原图实际存在的边。
        /// L2 消掉的异常边只有 phi 全部来源相同时才可恢复，否则保留洞，不猜寄存器版本。
        /// </summary>
        private void ExceptionCopies(ExceptionEntryPath path, List<ManagedStatement> statements)
        {
            var aliases = new Dictionary<Variable, Variable>();
            var from = path.Source.Block;
            var copies = new List<ManagedCopy>();
            foreach (var fragment in path.Bridges.Append(path.Entry))
            {
                if (from == fragment.Block) continue;
                var successor = from.Successors.FindLastIndex(b => b == fragment.Block);
                var incoming = successor >= 0 ? MachineFunction.PredecessorIndex(from, successor) : -1;
                foreach (var phi in fragment.Statements.OfType<Phi>())
                {
                    if (runtime.Contains(phi.Target) || exceptionValues.ContainsKey(phi.Target) || !exceptionDemand.Contains(phi.Target)) continue;
                    var sources = phi.Sources.Distinct().ToArray();
                    var source = incoming >= 0 ? phi.Sources[incoming] : sources.Length == 1 ? sources[0]
                        : throw Fail(phi.Address, $"异常区域 异常边 φ 来源未证成 {phi.Target} site=0x{path.Source.NativeExceptionSite:x}");
                    var seen = new HashSet<Variable>();
                    while (aliases.TryGetValue(source, out var previous) && seen.Add(source)) source = previous;
                    aliases[phi.Target] = source;
                    var target = Local(phi.Target);
                    var value = values.TryGetValue(source, out var constant) && constant is Const c
                        ? new ConstantValue(c.Value & Expr.Mask(target.Width), target.Type, target.Width) : Variable(source, target.Width);
                    copies.Add(new(target, Coerce(value, target.Type, phi.Address)));
                }
                from = fragment.Block;
            }
            // 并行复制不能因目的地与另一个来源重叠而改变值。
            var saved = copies.Select(c => (c.Target, Value: c.Value, Temp: StructLocal(c.Target.Type, c.Target.Width))).ToArray();
            foreach (var c in saved) statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Temp, c.Value));
            foreach (var c in saved) statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Target, c.Temp));
        }
        /// <summary>异常筛选的类型判断：catch 的 IsAssignableFrom 写成 isinst 比较，结果补零到 64 位。</summary>
        [CallRule(20)]
        private bool LowerExceptionTypeTarget(Call call, List<ManagedStatement> output)
        {
            if (!exceptionTypeTargets.TryGetValue(call, out var exceptionType) || !typeChecks.TryGetValue(call, out var exceptionObject)
                || call.Defines.FirstOrDefault() is not { } exceptionResult) return false;
            var matched = new ComparisonValue(Cond.Ne, new IsInstValue(RecoverAs(exceptionObject, types.Object, call.Address), exceptionType),
                new ConstantValue(0, exceptionType, 64), types.Boolean);
            output.Add(new ManagedAssignment(call.Address, Local(exceptionResult), Coerce(matched, types.UInt64, call.Address)));
            return true;
        }
    }
}
