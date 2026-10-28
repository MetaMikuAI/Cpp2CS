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

        /// <summary>删除纯定义后按保留语句重映射异常片段；调用及控制流边不变。</summary>
        private void RemoveDeadDefinitions()
        {
            var previous = exceptionLayout is { Succeeded: true } layout
                ? layout.Graph.Fragments.Select(f => f.Block).Distinct().ToDictionary(b => b, b => b.Statements.ToArray()) : null;
            Ssa.Propagate.RemoveDead(function);
            if (previous is null) return;
            foreach (var group in exceptionLayout!.Graph.Fragments.GroupBy(f => f.Block))
            {
                var retained = group.Key.Statements.ToHashSet(ReferenceEqualityComparer.Instance);
                var old = previous[group.Key];
                var positions = new int[old.Length + 1];
                for (var i = 0; i < old.Length; i++) positions[i + 1] = positions[i] + (retained.Contains(old[i]) ? 1 : 0);
                foreach (var fragment in group)
                {
                    fragment.First = positions[fragment.First];
                    fragment.Limit = positions[fragment.Limit];
                }
            }
        }

        /// <summary>插入的定义属于随后语句所在片段；同步其余片段的半开区间。</summary>
        private void InsertAnalysisStatement(Block block, int index, Stmt statement)
        {
            if (exceptionLayout is { Succeeded: true } layout)
                foreach (var fragment in layout.Graph.Fragments.Where(f => f.Block == block))
                {
                    if (fragment.First > index) fragment.First++;
                    if (fragment.Limit > index) fragment.Limit++;
                }
            block.Statements.Insert(index, statement);
        }

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
            // selector 分派剪枝后，外语异常清理路径的栈上备份可能已没有任何读取。
            var selectors = values.Where(p => p.Value is Intrinsic { Name: "eh_selector" }).Select(p => p.Key).ToHashSet();
            foreach (var store in blocks.SelectMany(b => b.Statements).OfType<Store>())
                if (store is { Target: FrameAddress address, Value: Use use } && selectors.Contains(use.Variable)
                    && !blocks.SelectMany(b => b.Statements).Where(s => !ReferenceEquals(s, store))
                        .SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Any(e =>
                            e is Load load && FrameOffset(load.Address) is { } offset
                                && offset < address.Offset + use.Width / 8 && offset + load.Width / 8 > address.Offset
                            || FrameOffset(e) is { } pointer && pointer >= address.Offset && pointer < address.Offset + use.Width / 8))
                    dropped.Add(store);
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

        private RecoveryResult<ManagedBody> BuildExceptionBody()
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
                    if (statement is Branch branch)
                    {
                        if ((normal.GetValueOrDefault(fragment.Id) ?? []).Length == 2) _ = Recover(branch.Condition, types.Boolean);
                    }
                    else
                    {
                        var translated = new List<ManagedStatement>();
                        // 失败由实际写出遍历登记；此遍历只收集已读取的来源。
                        if (Translate(fragment.Block, statement, translated) is not null) continue;
                        foreach (var value in translated.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                            .SelectMany(WalkRecoveryValue).OfType<LocalValue>()) exceptionDemand.Add(value.Variable);
                    }
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
                RecoveryFailure? LowerFragment()
                {
                    foreach (var path in layout.EntryPaths.Where(p => p.Source == fragment && active.Contains(p.Entry)))
                        if (ExceptionCopies(path, statements) is { } failure) return failure;
                    var successors = normal.GetValueOrDefault(fragment.Id) ?? [];
                    foreach (var statement in fragment.Statements)
                    {
                        if (dropped.Contains(statement)) continue;
                        if (statement is Define d && (runtime.Contains(d.Target) || exceptionValues.ContainsKey(d.Target) || !exceptionDemand.Contains(d.Target))) continue;
                        if (statement is Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch }) continue;
                        if (statement is Call { Op.Kind: OpKind.ResumeUnwind } resume)
                        {
                            if (!layout.Regions.Any(r => r.Kind == "fault" && r.Handler.Contains(fragment)))
                                return Fail(resume.Address, "异常区域 可达清理未映射为 fault");
                            statements.Add(new ManagedEndFault(resume.Address)); continue;
                        }
                        if (statement is Branch branch)
                        {
                            if (successors is [var only])
                            {
                                if (Emit(ExceptionEdge(fragment, only).Map(edge => new ManagedJump(branch.Address, edge)), statements) is { } failure) return failure;
                            }
                            else if (successors.Length == 2)
                            {
                                if (!Recover(branch.Condition, types.Boolean).Bind(Truth).TryGet(out var condition, out var failure)) return failure;
                                if (!ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Target)).TryGet(out var taken, out failure)) return failure;
                                if (!ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Fallthrough)).TryGet(out var other, out failure)) return failure;
                                statements.Add(new ManagedBranch(branch.Address, condition, taken, other));
                            }
                            else return Fail(branch.Address, "异常区域 分支后继未证成");
                            continue;
                        }
                        if (statement is Jump jump)
                        {
                            if (successors is not [var only]) return Fail(jump.Address, "异常区域 跳转后继未证成");
                            if (Emit(ExceptionEdge(fragment, only).Map(edge => new ManagedJump(jump.Address, edge)), statements) is { } failure) return failure;
                            continue;
                        }
                        if (statement is IndirectJump table && switchIndices.TryGetValue(table, out var index))
                        {
                            var targets = successors.ToDictionary(f => f.Block.Start);
                            if (table.Targets.Any(t => !targets.ContainsKey(t))) return Fail(table.Address, "异常区域 switch 后继未证成");
                            if (!Index(index).TryGet(out var selector, out var failure)) return failure;
                            var edges = new List<ManagedEdge>();
                            foreach (var target in table.Targets)
                            {
                                if (!ExceptionEdge(fragment, targets[target]).TryGet(out var edge, out failure)) return failure;
                                edges.Add(edge);
                            }
                            statements.Add(new ManagedSwitch(table.Address, selector, edges));
                            continue;
                        }
                        if (statement is Call { Op.Kind: OpKind.ThrowManaged or OpKind.Rethrow, Arguments: [Use value] } rethrow
                            && exceptionValues.TryGetValue(value.Variable, out var current)
                            // rethrow 指向最内层活动 catch；内层 catch 中再次抛出外层保存对象必须用 throw。
                            && caughtExceptions.Where(p => p.Key.Handler.Contains(fragment)).OrderBy(p => p.Key.Handler.Count).FirstOrDefault().Value == current)
                        { statements.Add(new ManagedRethrow(rethrow.Address)); continue; }
                        if (ledger.TryGetDiagnosis(statement, out var cause)) return Derived(cause, "异常区域 语句已诊断");
                        if (Translate(fragment.Block, statement, statements) is { } translationFailure) return translationFailure;
                    }
                    if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedRethrow or ManagedEndFault or ManagedCall { Tail: true }))
                    {
                        if (successors is [var only])
                        {
                            if (Emit(ExceptionEdge(fragment, only).Map(edge => new ManagedJump(fragment.Block.End, edge)), statements) is { } failure) return failure;
                        }
                        else return Fail(fragment.Block.Start, "异常区域 片段缺少终结方式");
                    }
                    return null;
                }
                if (LowerFragment() is { } failure)
                {
                    Record(failure, fragment.Block.Start);
                    statements.Add(new ManagedHole(failure.Address == 0 ? fragment.Block.Start : failure.Address, failure.Message, true));
                }
                output.Add(new(FragmentLabel(fragment), statements));
            }
            var body = new ManagedBody(method, output)
            {
                Regions = layout.Regions.OrderByDescending(r => r.Try.Count + r.Handler.Count).Select(r => new ManagedRegion(
                    order.Where(r.Try.Contains).Select(FragmentLabel).ToArray(), FragmentLabel(r.Entry),
                    order.Where(r.Handler.Contains).Select(FragmentLabel).ToArray(), caughtExceptions.GetValueOrDefault(r),
                    r.Kind == "catch" ? ManagedRegionKind.Catch : ManagedRegionKind.Fault)).ToArray(),
            };
            return RouteExceptionSources(body, layout, order);
        }

        private RecoveryResult<ManagedEdge> ExceptionEdge(ExceptionFragment from, ExceptionFragment to)
        {
            if (from.Block == to.Block) return new ManagedEdge(FragmentLabel(to), []);
            var successor = from.Block.NormalSuccessors.ToList().IndexOf(to.Block);
            if (successor < 0) return Fail(from.Block.Start, "异常区域 普通边没有原始 SSA 来源");
            return Edge(from.Block, successor, to.Block.Start).Map(edge => edge with { Target = FragmentLabel(to) });
        }

        /// <summary>
        /// 异常边的 phi 在可能抛出前快照。空桥逐级代入来源；普通边索引只用于原图实际存在的边。
        /// L2 消掉的异常边从原生存储的到达赋值取值；被传播删去的复制定义仍是赋值证据。
        /// </summary>
        private RecoveryFailure? ExceptionCopies(ExceptionEntryPath path, List<ManagedStatement> statements)
        {
            var aliases = new Dictionary<Variable, Expr>();
            var copies = new List<ManagedCopy>();
            Expr Resolve(Expr expression) => ExprMap.Map(expression, e =>
            {
                if (e is not Use use) return null;
                var value = aliases.GetValueOrDefault(use.Variable)
                    ?? (values.GetValueOrDefault(use.Variable) is Const constant ? constant : null);
                if (value is null) return null;
                return value.Width == use.Width ? value : Fold.Simplify(new Ir.Convert(
                    value.Width > use.Width ? ConvKind.Truncate : ConvKind.ZeroExtend, value, use.Width));
            });
            RecoveryFailure? Copy(Variable variable, Expr expression, ulong address)
            {
                var value = Resolve(expression);
                aliases[variable] = value;
                if (!Local(variable).TryGet(out var target, out var failure)) return failure;
                if (!Recover(value, target.Type).Bind(recovered => Coerce(recovered, target.Type, address)).TryGet(out var result, out failure)) return failure;
                copies.Add(new(target, result));
                return null;
            }
            var from = path.Source.Block;
            var previousFragment = path.Source;
            foreach (var fragment in path.Bridges.Append(path.Entry))
            {
                var successor = from.Successors.FindLastIndex(b => b == fragment.Block);
                var incoming = successor >= 0 ? MachineFunction.PredecessorIndex(from, successor) : -1;
                foreach (var phi in fragment.Statements.OfType<Phi>().Where(_ => from != fragment.Block))
                {
                    if (runtime.Contains(phi.Target) || exceptionValues.ContainsKey(phi.Target) || !exceptionDemand.Contains(phi.Target)) continue;
                    var sources = phi.Sources.Distinct().ToArray();
                    var source = incoming >= 0 ? phi.Sources[incoming] : sources.Length == 1 ? sources[0]
                        : ExceptionReachingSource(previousFragment, phi, previousFragment == path.Source);
                    if (source is null) return Fail(phi.Address, $"异常区域 异常边 φ 来源未证成 {phi.Target} site=0x{path.Source.NativeExceptionSite:x}");
                    if (Copy(phi.Target, new Use(source, phi.Target.Width), phi.Address) is { } failure) return failure;
                }
                // 桥中的纯复制也被区域图消去；逐级代入后与 phi 一起在调用前快照。
                if (fragment != path.Entry)
                    foreach (var define in fragment.Statements.OfType<Define>())
                        if (!runtime.Contains(define.Target) && !exceptionValues.ContainsKey(define.Target)
                            && exceptionDemand.Contains(define.Target))
                            if (Copy(define.Target, define.Value, define.Address) is { } failure) return failure;
                from = fragment.Block;
                previousFragment = fragment;
            }
            // 并行复制不能因目的地与另一个来源重叠而改变值。
            var saved = copies.Select(c => (c.Target, Value: c.Value, Temp: StructLocal(c.Target.Type, c.Target.Width))).ToArray();
            foreach (var c in saved) statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Temp, c.Value));
            foreach (var c in saved) statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Target, c.Temp));
            return null;
        }

        /// <summary>仅追溯调用不会破坏的寄存器和已提升栈槽；不同前驱必须给出同一版本，不补猜缺失的赋值。</summary>
        private Variable? ExceptionReachingSource(ExceptionFragment from, Phi phi, bool beforeCall)
        {
            var storage = phi.Target.Storage;
            if (storage.Bank != Bank.Stack && (storage.Bank != Bank.Gpr || storage.Index == 30 || !CalleeSaved.Contains(storage))) return null;
            var dead = function.Dead.Where(d => d.Define.Target.Storage == storage).ToLookup(d => d.Block, d => d.Define);
            var reaching = new Dictionary<(Block Block, int End, ulong Boundary), Variable?>();
            var cycles = 0;
            Variable? Reaching(Block block, int end, ulong boundary, HashSet<Block> active)
            {
                var key = (block, end, boundary);
                if (reaching.TryGetValue(key, out var cached)) return cached;
                var removed = dead[block].Where(d => d.Address < boundary).MaxBy(d => d.Address);
                for (var i = end - 1; i >= 0; i--)
                {
                    var statement = block.Statements[i];
                    if (removed is not null && removed.Address > statement.Address) return removed.Target;
                    if (statement is Define define && define.Target.Storage == storage) return define.Target;
                    if (statement is Phi merged && merged.Target.Storage == storage) return merged.Target;
                    if (statement is Call call && call.Defines.FirstOrDefault(v => v?.Storage == storage) is { } result) return result;
                }
                if (removed is not null) return removed.Target;
                if (block == function.EntryBlock) return new(storage, 0);
                if (!active.Add(block)) { cycles++; return null; }
                var before = cycles;
                Variable? reached = null;
                foreach (var parent in block.Predecessors.Distinct())
                {
                    var incoming = Reaching(parent, parent.Statements.Count, ulong.MaxValue, active);
                    if (incoming is null || reached is not null && reached != incoming) { reached = null; break; }
                    reached = incoming;
                }
                active.Remove(block);
                // 环上的拒绝依赖当前递归路径；只复用没有遇到回边的结果。
                if (cycles == before) reaching[key] = reached;
                return reached;
            }
            Expr Value(Variable variable)
            {
                var seen = new HashSet<Variable>();
                while (seen.Add(variable))
                {
                    var value = values.GetValueOrDefault(variable) ?? function.Dead.FirstOrDefault(d => d.Define.Target == variable).Define?.Value;
                    if (value is Const constant) return constant;
                    if (value is not Use use || use.Width != variable.Width) break;
                    variable = use.Variable;
                }
                return new Use(variable, variable.Width);
            }
            var end = beforeCall ? from.First : from.Limit;
            var boundary = end < from.Block.Statements.Count ? from.Block.Statements[end].Address : ulong.MaxValue;
            if (Reaching(from.Block, end, boundary, []) is not { } reached) return null;
            var expression = Value(reached);
            return phi.Sources.FirstOrDefault(source => Value(source) == expression);
        }
        /// <summary>异常筛选的类型判断：catch 的 IsAssignableFrom 写成 isinst 比较，结果补零到 64 位。</summary>
        [CallRule(20)]
        private RecoveryResult<bool> LowerExceptionTypeTarget(Call call, List<ManagedStatement> output)
        {
            if (!exceptionTypeTargets.TryGetValue(call, out var exceptionType) || !typeChecks.TryGetValue(call, out var exceptionObject)
                || call.Defines.FirstOrDefault() is not { } exceptionResult) return false;
            if (!RecoverAs(exceptionObject, types.Object, call.Address).TryGet(out var value, out var failure)) return failure;
            var matched = new ComparisonValue(Cond.Ne, new IsInstValue(value, exceptionType),
                new ConstantValue(0, exceptionType, 64), types.Boolean);
            if (Assign(call.Address, exceptionResult, () => Coerce(matched, types.UInt64, call.Address), output) is { } assignmentFailure) return assignmentFailure;
            return true;
        }
    }
}
