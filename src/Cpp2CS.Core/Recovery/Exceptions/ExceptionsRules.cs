using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class ExceptionsRules
{
    [InvocationOutputRule(90)]
    internal static bool ThrowingInvocation(this LoweringScope ctx, Call call, AbiSignature signature, Dictionary<Storage, Expr> registers, ManagedInvocation invocation, List<ManagedStatement> output)
    {
        if (!ctx.ExpandThrowCalls || call is not { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } || invocation is not { Virtual: false, Receiver: null } || ctx.Values.ThrowingConstructor(invocation.Method, target.Value) is not { } created || !ManagedAccess.Method(ctx.types, ctx.method.Method.Owner, created.Constructor, created.Type))
            return false;
        output.Add(new ManagedThrow(call.Address, created with { Arguments = created.Arguments.Select(v => v is ArgumentValue argument ? invocation.Arguments[argument.Index] : v).ToArray(), }));
        return true;
    }

    internal static ulong FragmentLabel(ExceptionFragment fragment) => NameSupply.ExceptionLabelBase + (uint)fragment.Id;
    internal static void RemoveDeadDefinitions(this RecoveryScope ctx)
    {
        var previous = ctx.State.Exceptions.exceptionLayout is { Succeeded: true } layout ? layout.Graph.Fragments.Select(f => f.Block).Distinct().ToDictionary(b => b, b => b.Statements.ToArray()) : null;
        Cpp2CS.Machine.Ssa.Propagate.RemoveDead(ctx.function);
        if (previous is null)
            return;
        foreach (var group in ctx.State.Exceptions.exceptionLayout!.Graph.Fragments.GroupBy(f => f.Block))
        {
            var retained = group.Key.Statements.ToHashSet(ReferenceEqualityComparer.Instance);
            var old = previous[group.Key];
            var positions = new int[old.Length + 1];
            for (var i = 0; i < old.Length; i++)
                positions[i + 1] = positions[i] + (retained.Contains(old[i]) ? 1 : 0);
            foreach (var fragment in group)
            {
                fragment.First = positions[fragment.First];
                fragment.Limit = positions[fragment.Limit];
            }
        }
    }

    internal static void InsertAnalysisStatement(this RecoveryScope ctx, Block block, int index, Stmt statement)
    {
        if (ctx.State.Exceptions.exceptionLayout is { Succeeded: true } layout)
            foreach (var fragment in layout.Graph.Fragments.Where(f => f.Block == block))
            {
                if (fragment.First > index)
                    fragment.First++;
                if (fragment.Limit > index)
                    fragment.Limit++;
            }

        ctx.Rewriter.Insert(block, index, statement);
    }

    internal static bool PrepareExceptionRegions(this RecoveryScope ctx)
    {
        ctx.State.Exceptions.exceptionLayout = ExceptionRegionBuilder.Build(ctx.facts, ctx.function);
        if (!ctx.State.Exceptions.exceptionLayout.Succeeded)
            return false;
        var catchEntries = new Dictionary<ExceptionRegionPlan, Call>();
        foreach (var region in ctx.State.Exceptions.exceptionLayout.Regions.Where(r => r.Kind == "catch"))
        {
            var entries = region.Handler.SelectMany(f => f.Statements).OfType<Call>().Where(c => c.Op?.Kind == OpKind.BeginCatch).ToArray();
            if (entries is not [var begin])
            {
                ctx.State.Exceptions.exceptionLayout = ctx.State.Exceptions.exceptionLayout with
                {
                    Reason = "catch 入口未证明",
                    Detail = $"BeginCatch 数量 {entries.Length}"
                };
                return false;
            }

            catchEntries.Add(region, begin);
        }

        var incoming = new Dictionary<Block, HashSet<int>>();
        void KeepEdge(Block from, Block to, bool exceptional)
        {
            if (from == to)
                return;
            var successor = exceptional ? from.Successors.FindLastIndex(b => b == to) : from.NormalSuccessors.ToList().IndexOf(to);
            if (successor < 0)
                return;
            if (!incoming.TryGetValue(to, out var indices))
                incoming[to] = indices = [];
            indices.Add(MachineFunction.PredecessorIndex(from, successor));
        }

        var fragments = ctx.State.Exceptions.exceptionLayout.Graph.Fragments.ToDictionary(f => f.Id);
        foreach (var edge in ctx.State.Exceptions.exceptionLayout.Edges.Where(e => e[2] == 0))
            KeepEdge(fragments[edge[0]].Block, fragments[edge[1]].Block, false);
        foreach (var path in ctx.State.Exceptions.exceptionLayout.EntryPaths)
        {
            var from = path.Source.Block;
            foreach (var part in path.Bridges.Append(path.Entry))
            {
                KeepEdge(from, part.Block, true);
                from = part.Block;
            }
        }

        // 类型推断只读已保留的入边；真正复制仍读取原图完整 phi 及原始前驱索引。
        foreach (var (block, indices) in incoming)
            foreach (var phi in block.Statements.OfType<Phi>())
                ctx.State.Exceptions.exceptionPhis[phi.Target] = phi with
                {
                    Sources = indices.Order().Select(i => phi.Sources[i]).ToArray()
                };
        var kept = ctx.State.Exceptions.exceptionLayout.Kept.Concat(ctx.State.Exceptions.exceptionLayout.EntryPaths.SelectMany(p => p.Bridges)).Select(f => f.Block).ToHashSet();
        ctx.blocks = ctx.function.Blocks.Where(kept.Contains).ToArray();
        foreach (var region in ctx.State.Exceptions.exceptionLayout.Regions.Where(r => r.Kind == "catch"))
        {
            var exception = ctx.StructLocal(ctx.types.Corlib("System.Exception"), 64);
            ctx.State.Exceptions.caughtExceptions.Add(region, exception);
            ctx.State.Exceptions.exceptionValues[exception.Variable] = exception;
            ctx.State.Types.known[exception.Variable] = exception.Type;
            var begin = catchEntries[region];
            foreach (var variable in begin.Defines.OfType<Variable>())
                ctx.State.Exceptions.wrappers[variable] = exception;
        }

        return true;
    }

    [Analysis("异常值", 10)]
    internal static void AnalyzeExceptionValues(this RecoveryScope ctx)
    {
        if (ctx.State.Exceptions.exceptionLayout is not { Succeeded: true })
            return;
        foreach (var (variable, expression) in ctx.values)
            if (expression is Intrinsic { Name: "eh_exception" or "eh_selector" })
                ctx.State.Runtime.runtime.Add(variable);
        foreach (var variable in ctx.State.Exceptions.wrappers.Keys)
            ctx.State.Runtime.runtime.Add(variable);
        var (closedWrappers, closedExceptions) = ExceptionValueClosure.Close(new MethodView(ctx.blocks, ctx.State.Exceptions.exceptionPhis).Statements, ctx.State.Exceptions.wrappers, ctx.State.Exceptions.exceptionValues);
        foreach (var (variable, wrapper) in closedWrappers)
            ctx.State.Exceptions.wrappers.TryAdd(variable, wrapper);
        foreach (var (variable, exception) in closedExceptions)
            ctx.State.Exceptions.exceptionValues.TryAdd(variable, exception);
        foreach (var variable in ctx.State.Exceptions.wrappers.Keys)
            ctx.State.Runtime.runtime.Add(variable);
        foreach (var (variable, exception) in ctx.State.Exceptions.exceptionValues)
            ctx.State.Types.known[variable] = exception.Type;
        // selector 分派剪枝后，外语异常清理路径的栈上备份可能已没有任何读取。
        var selectors = ctx.values.Where(p => p.Value is Intrinsic { Name: "eh_selector" }).Select(p => p.Key).ToHashSet();
        foreach (var store in ctx.blocks.SelectMany(b => b.Statements).OfType<Store>())
            if (store is { Target: FrameAddress address, Value: Use use } && selectors.Contains(use.Variable) && !ctx.blocks.SelectMany(b => b.Statements).Where(s => !ReferenceEquals(s, store)).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Any(e => e is Load load && ctx.FrameOffset(load.Address) is { } offset && offset < address.Offset + use.Width / 8 && offset + load.Width / 8 > address.Offset || ctx.FrameOffset(e) is { } pointer && pointer >= address.Offset && pointer < address.Offset + use.Width / 8))
                ctx.State.Lowering.dropped.Add(store);
    }

    internal static bool PrepareExceptionTypeChecks(this RecoveryScope ctx)
    {
        if (ctx.State.Exceptions.exceptionLayout is not { Succeeded: true })
            return false;
        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
            if (call is { Op.Kind: OpKind.IsAssignableFrom, Arguments: [var target, Use klass] } && ctx.Expand(target) is Symbol { Kind: SymbolKind.Class, Value: TypeRef type } && ctx.values.TryGetValue(klass.Variable, out var value) && value is Load { Width: 64, Address: Use obj } && ctx.State.Exceptions.exceptionValues.ContainsKey(obj.Variable))
            {
                // E1 wrapper+0 已证明为非空托管异常；运行时类检查等价于对同一对象 isinst 后与 null 比较。
                ctx.State.Runtime.objectClasses[klass.Variable] = obj;
                ctx.State.Runtime.typeChecks[call] = obj;
                ctx.State.Exceptions.exceptionTypeTargets[call] = type;
                ctx.State.Runtime.runtime.Add(klass.Variable);
            }

        return ctx.State.Exceptions.exceptionTypeTargets.Count != 0;
    }

    internal static RecoveryResult<ManagedBody> BuildExceptionBody(this RecoveryScope ctx)
    {
        var layout = ctx.State.Exceptions.exceptionLayout!;
        var byId = layout.Graph.Fragments.ToDictionary(f => f.Id);
        var normal = layout.Edges.Where(e => e[2] == 0).GroupBy(e => e[0]).ToDictionary(g => g.Key, g => g.Select(e => byId[e[1]]).ToArray());
        // 只有 C++ 簿记的 cleanup 没有 CIL 入口，不把其 Resume 误写成普通可达代码。
        var active = new HashSet<ExceptionFragment>();
        var pending = new Stack<ExceptionFragment>(layout.Regions.Select(r => r.Entry).Prepend(layout.Graph.Entry));
        while (pending.TryPop(out var reached))
            if (active.Add(reached))
                foreach (var next in normal.GetValueOrDefault(reached.Id) ?? [])
                    pending.Push(next);
        var order = layout.Order.Where(active.Contains).ToArray();
        // selector 剪枝后，原图还可能保留只给外来路径或原生调用临时寄存器使用的 phi。
        // 从实际托管语句的读取回溯 SSA；有访存的定义仍是根，不能把可能抛出的加载当死代码删除。
        ctx.State.Exceptions.collectingExceptionDemand = true;
        foreach (var fragment in order)
            foreach (var statement in fragment.Statements)
            {
                if (ctx.State.Lowering.dropped.Contains(statement) || statement is Phi or Nop or Jump or Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch or OpKind.ResumeUnwind })
                    continue;
                if (statement is Define define)
                {
                    if (ctx.State.Runtime.runtime.Contains(define.Target) || ctx.State.Exceptions.exceptionValues.ContainsKey(define.Target) || !ExprMap.Walk(define.Value).Any(e => e is Load))
                        continue;
                    ctx.State.Exceptions.exceptionDemand.Add(define.Target);
                }

                if (statement is Branch branch)
                {
                    if ((normal.GetValueOrDefault(fragment.Id) ?? []).Length == 2)
                        _ = ctx.Recover(branch.Condition, ctx.types.Boolean);
                }
                else
                {
                    var translated = new List<ManagedStatement>();
                    // 失败由实际写出遍历登记；此遍历只收集已读取的来源。
                    if (ctx.Translate(fragment.Block, statement, translated) is not null)
                        continue;
                    foreach (var value in translated.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(FragmentsRules.WalkRecoveryValue).OfType<LocalValue>())
                        ctx.State.Exceptions.exceptionDemand.Add(value.Variable);
                }
            }

        ctx.State.Exceptions.collectingExceptionDemand = false;
        var work = new Queue<Variable>(ctx.State.Exceptions.exceptionDemand);
        while (work.TryDequeue(out var variable))
        {
            var sources = ctx.values.TryGetValue(variable, out var value) ? ExprMap.Walk(value).OfType<Use>().Select(u => u.Variable) : ctx.phis.TryGetValue(variable, out var phi) ? phi.Sources : [];
            foreach (var source in sources)
                if (ctx.State.Exceptions.exceptionDemand.Add(source))
                    work.Enqueue(source);
        }

        var output = new List<ManagedBlock>();
        foreach (var fragment in order)
        {
            var statements = new List<ManagedStatement>();
            RecoveryFailure? LowerFragment()
            {
                foreach (var path in layout.EntryPaths.Where(p => p.Source == fragment && active.Contains(p.Entry)))
                    if (ctx.ExceptionCopies(path, statements) is { } failure)
                        return failure;
                var successors = normal.GetValueOrDefault(fragment.Id) ?? [];
                foreach (var statement in fragment.Statements)
                {
                    if (ctx.State.Lowering.dropped.Contains(statement))
                        continue;
                    if (statement is Define d && (ctx.State.Runtime.runtime.Contains(d.Target) || ctx.State.Exceptions.exceptionValues.ContainsKey(d.Target) || !ctx.State.Exceptions.exceptionDemand.Contains(d.Target)))
                        continue;
                    if (statement is Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch })
                        continue;
                    if (statement is Call { Op.Kind: OpKind.ResumeUnwind } resume)
                    {
                        if (!layout.Regions.Any(r => r.Kind == "fault" && r.Handler.Contains(fragment)))
                            return RecoveryDiagnostics.Fail(resume.Address, "异常区域 可达清理未映射为 fault", rule: "BuildExceptionBody");
                        statements.Add(new ManagedEndFault(resume.Address));
                        continue;
                    }

                    if (statement is Branch branch)
                    {
                        if (successors is [var only])
                        {
                            if (BodyLowering.Emit(ctx.ExceptionEdge(fragment, only).Map(edge => new ManagedJump(branch.Address, edge)), statements) is { } failure)
                                return failure;
                        }
                        else if (successors.Length == 2)
                        {
                            if (!ctx.Recover(branch.Condition, ctx.types.Boolean).Bind(ValueRecovery.Truth).TryGet(out var condition, out var failure))
                                return failure;
                            if (!ctx.ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Target)).TryGet(out var taken, out failure))
                                return failure;
                            if (!ctx.ExceptionEdge(fragment, successors.Single(f => f.Block.Start == branch.Fallthrough)).TryGet(out var other, out failure))
                                return failure;
                            statements.Add(new ManagedBranch(branch.Address, condition, taken, other));
                        }
                        else
                            return RecoveryDiagnostics.Fail(branch.Address, "异常区域 分支后继未证成", rule: "BuildExceptionBody");
                        continue;
                    }

                    if (statement is Jump jump)
                    {
                        if (successors is not [var only])
                            return RecoveryDiagnostics.Fail(jump.Address, "异常区域 跳转后继未证成", rule: "BuildExceptionBody");
                        if (BodyLowering.Emit(ctx.ExceptionEdge(fragment, only).Map(edge => new ManagedJump(jump.Address, edge)), statements) is { } failure)
                            return failure;
                        continue;
                    }

                    if (statement is IndirectJump table && ctx.State.Calls.switchIndices.TryGetValue(table, out var index))
                    {
                        var targets = successors.ToDictionary(f => f.Block.Start);
                        if (table.Targets.Any(t => !targets.ContainsKey(t)))
                            return RecoveryDiagnostics.Fail(table.Address, "异常区域 switch 后继未证成", rule: "BuildExceptionBody");
                        if (!ctx.Index(index).TryGet(out var selector, out var failure))
                            return failure;
                        var edges = new List<ManagedEdge>();
                        foreach (var target in table.Targets)
                        {
                            if (!ctx.ExceptionEdge(fragment, targets[target]).TryGet(out var edge, out failure))
                                return failure;
                            edges.Add(edge);
                        }

                        statements.Add(new ManagedSwitch(table.Address, selector, edges));
                        continue;
                    }

                    if (statement is Call { Op.Kind: OpKind.ThrowManaged or OpKind.Rethrow, Arguments: [Use value] } rethrow && ctx.State.Exceptions.exceptionValues.TryGetValue(value.Variable, out var current) // rethrow 指向最内层活动 catch；内层 catch 中再次抛出外层保存对象必须用 throw。
                    && ctx.State.Exceptions.caughtExceptions.Where(p => p.Key.Handler.Contains(fragment)).OrderBy(p => p.Key.Handler.Count).FirstOrDefault().Value == current)
                    {
                        statements.Add(new ManagedRethrow(rethrow.Address));
                        continue;
                    }

                    if (ctx.ledger.TryGetDiagnosis(statement, out var cause))
                        return RecoveryDiagnostics.Derived(cause, "异常区域 语句已诊断");
                    if (ctx.Translate(fragment.Block, statement, statements) is { } translationFailure)
                        return translationFailure;
                }

                if (statements.LastOrDefault() is not (ManagedReturn or ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedRethrow or ManagedEndFault or ManagedCall { Tail: true }))
                {
                    if (successors.Length == 0 && fragment.Statements.LastOrDefault() is Call { Kind: CallKind.Tail, Op.Kind: OpKind.EndCatch }
                        && ManagedTypes.IsVoid(ctx.State.Signature.returnType))
                        statements.Add(new ManagedReturn(fragment.Block.End, null));
                    else if (successors.Length == 0 && ctx.NonReturningManagedCall(fragment.Statements.LastOrDefault()))
                        statements.Add(new ManagedThrow(fragment.Block.End, new ConstantValue(0, ctx.types.Corlib("System.Exception"), 64)));
                    else if (successors is [var only])
                    {
                        if (BodyLowering.Emit(ctx.ExceptionEdge(fragment, only).Map(edge => new ManagedJump(fragment.Block.End, edge)), statements) is { } failure)
                            return failure;
                    }
                    else
                        return RecoveryDiagnostics.Fail(fragment.Block.Start, "异常区域 片段缺少终结方式", rule: "BuildExceptionBody");
                }

                return null;
            }

            if (LowerFragment() is { } failure)
            {
                ctx.Record(failure, fragment.Block.Start);
                statements.Add(new ManagedHole(failure.Address == 0 ? fragment.Block.Start : failure.Address, failure.Message, true));
            }

            output.Add(new(ExceptionsRules.FragmentLabel(fragment), statements));
        }

        var body = new ManagedBody(ctx.method, output)
        {
            Regions = layout.Regions.OrderByDescending(r => r.Try.Count + r.Handler.Count).Select(r => new ManagedRegion(order.Where(r.Try.Contains).Select(ExceptionsRules.FragmentLabel).ToArray(), ExceptionsRules.FragmentLabel(r.Entry), order.Where(r.Handler.Contains).Select(ExceptionsRules.FragmentLabel).ToArray(), ctx.State.Exceptions.caughtExceptions.GetValueOrDefault(r), r.Kind == "catch" ? ManagedRegionKind.Catch : ManagedRegionKind.Fault)).ToArray(),
        };
        return ctx.RouteExceptionSources(body, layout, order);
    }

    internal static RecoveryResult<ManagedEdge> ExceptionEdge(this RecoveryScope ctx, ExceptionFragment from, ExceptionFragment to)
    {
        if (from.Block == to.Block)
            return new ManagedEdge(ExceptionsRules.FragmentLabel(to), []);
        var successor = from.Block.NormalSuccessors.ToList().IndexOf(to.Block);
        if (successor < 0)
            return RecoveryDiagnostics.Fail(from.Block.Start, "异常区域 普通边没有原始 SSA 来源", rule: "ExceptionEdge");
        return ctx.Edge(from.Block, successor, to.Block.Start).Map(edge => edge with { Target = ExceptionsRules.FragmentLabel(to) });
    }

    internal static RecoveryFailure? ExceptionCopies(this RecoveryScope ctx, ExceptionEntryPath path, List<ManagedStatement> statements)
    {
        var aliases = new Dictionary<Variable, Expr>();
        var copies = new List<ManagedCopy>();
        Expr Resolve(Expr expression) => ExprMap.Map(expression, e =>
        {
            if (e is not Use use)
                return null;
            var value = aliases.GetValueOrDefault(use.Variable) ?? (ctx.values.GetValueOrDefault(use.Variable) is Const constant ? constant : null);
            if (value is null)
                return null;
            return value.Width == use.Width ? value : Fold.Simplify(new Ir.Convert(value.Width > use.Width ? ConvKind.Truncate : ConvKind.ZeroExtend, value, use.Width));
        });
        RecoveryFailure? Copy(Variable variable, Expr expression, ulong address)
        {
            var value = Resolve(expression);
            aliases[variable] = value;
            if (!ctx.Local(variable).TryGet(out var target, out var failure))
                return failure;
            if (!ctx.Recover(value, target.Type).Bind(recovered => ctx.Coerce(recovered, target.Type, address)).TryGet(out var result, out failure))
                return failure;
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
                if (ctx.State.Runtime.runtime.Contains(phi.Target) || ctx.State.Exceptions.exceptionValues.ContainsKey(phi.Target) || !ctx.State.Exceptions.exceptionDemand.Contains(phi.Target))
                    continue;
                var sources = phi.Sources.Distinct().ToArray();
                var source = incoming >= 0 ? phi.Sources[incoming] : sources.Length == 1 ? sources[0] : ctx.ExceptionReachingSource(previousFragment, phi, previousFragment == path.Source);
                if (source is null)
                    return RecoveryDiagnostics.Fail(phi.Address, $"异常区域 异常边 φ 来源未证成 {phi.Target} site=0x{path.Source.NativeExceptionSite:x}", rule: "ExceptionCopies");
                if (Copy(phi.Target, new Use(source, phi.Target.Width), phi.Address) is { } failure)
                    return failure;
            }

            // 桥中的纯复制也被区域图消去；逐级代入后与 phi 一起在调用前快照。
            if (fragment != path.Entry)
                foreach (var define in fragment.Statements.OfType<Define>())
                    if (!ctx.State.Runtime.runtime.Contains(define.Target) && !ctx.State.Exceptions.exceptionValues.ContainsKey(define.Target) && ctx.State.Exceptions.exceptionDemand.Contains(define.Target))
                        if (Copy(define.Target, define.Value, define.Address) is { } failure)
                            return failure;
            from = fragment.Block;
            previousFragment = fragment;
        }

        // 并行复制不能因目的地与另一个来源重叠而改变值。
        var saved = copies.Select(c => (c.Target, Value: c.Value, Temp: ctx.StructLocal(c.Target.Type, c.Target.Width))).ToArray();
        foreach (var c in saved)
            statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Temp, c.Value));
        foreach (var c in saved)
            statements.Add(new ManagedAssignment(path.Source.NativeExceptionSite ?? from.Start, c.Target, c.Temp));
        return null;
    }

    internal static Variable? ExceptionReachingSource(this RecoveryScope ctx, ExceptionFragment from, Phi phi, bool beforeCall)
    {
        var storage = phi.Target.Storage;
        if (storage.Bank != Bank.Stack && (storage.Bank != Bank.Gpr || storage.Index == 30 || !MethodRecovery.CalleeSaved.Contains(storage)))
            return null;
        Expr Value(Variable variable)
        {
            var seen = new HashSet<Variable>();
            while (seen.Add(variable))
            {
                var value = ctx.values.GetValueOrDefault(variable) ?? ctx.function.Dead.FirstOrDefault(d => d.Define.Target == variable).Define?.Value;
                if (value is Const constant)
                    return constant;
                if (value is not Use use || use.Width != variable.Width)
                    break;
                variable = use.Variable;
            }

            return new Use(variable, variable.Width);
        }

        var end = beforeCall ? from.First : from.Limit;
        var boundary = end < from.Block.Statements.Count ? from.Block.Statements[end].Address : ulong.MaxValue;
        var values = ExceptionReachingDefinitions(ctx.function, from.Block, end, boundary, storage).Select(Value).Distinct().ToArray();
        if (values is not [var expression])
            return null;
        return phi.Sources.FirstOrDefault(source => Value(source) == expression);
    }

    /// <summary>反向收集每条路径的最近定义；没有写入的回边不贡献新来源，不能把它当作未定义值。</summary>
    internal static Variable[] ExceptionReachingDefinitions(MachineFunction function, Block start, int end, ulong boundary, Storage storage)
    {
        var dead = function.Dead.Where(d => d.Define.Target.Storage == storage).ToLookup(d => d.Block, d => d.Define);
        var seen = new HashSet<(Block, int, ulong)>();
        var pending = new Stack<(Block, int, ulong)>();
        var sources = new HashSet<Variable>();
        pending.Push((start, end, boundary));
        Variable? Nearest(Block block, int limit, ulong before)
        {
            var removed = dead[block].Where(d => d.Address < before).MaxBy(d => d.Address);
            for (var i = limit - 1; i >= 0; i--)
            {
                var statement = block.Statements[i];
                if (removed is not null && removed.Address > statement.Address) return removed.Target;
                if (statement is Define define && define.Target.Storage == storage) return define.Target;
                if (statement is Phi phi && phi.Target.Storage == storage) return phi.Target;
                if (statement is Call call && call.Defines.FirstOrDefault(v => v?.Storage == storage) is { } result) return result;
            }
            return removed?.Target;
        }
        while (pending.TryPop(out var position))
        {
            if (!seen.Add(position)) continue;
            var (block, limit, before) = position;
            if (Nearest(block, limit, before) is { } source) sources.Add(source);
            else if (block == function.EntryBlock) sources.Add(new(storage, 0));
            else if (block.Predecessors.Count == 0) return [];
            else foreach (var parent in block.Predecessors.Distinct()) pending.Push((parent, parent.Statements.Count, ulong.MaxValue));
        }
        return sources.ToArray();
    }

    /// <summary>异常筛选的类型判断：catch 的 IsAssignableFrom 写成 isinst 比较，结果补零到 64 位。</summary>
    [CallRule(20)]
    internal static RecoveryResult<bool> LowerExceptionTypeTarget(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (!ctx.State.Exceptions.exceptionTypeTargets.TryGetValue(call, out var exceptionType) || !ctx.State.Runtime.typeChecks.TryGetValue(call, out var exceptionObject) || call.Defines.FirstOrDefault() is not { } exceptionResult)
            return false;
        if (!ctx.Values.RecoverAs(exceptionObject, ctx.types.Object, call.Address).TryGet(out var value, out var failure))
            return failure;
        var matched = new ComparisonValue(Cond.Ne, new IsInstValue(value, exceptionType), new ConstantValue(0, exceptionType, 64), ctx.types.Boolean);
        if (ctx.Values.Assign(call.Address, exceptionResult, () => ctx.Values.Coerce(matched, ctx.types.UInt64, call.Address), output) is { } assignmentFailure)
            return assignmentFailure;
        return true;
    }
}
