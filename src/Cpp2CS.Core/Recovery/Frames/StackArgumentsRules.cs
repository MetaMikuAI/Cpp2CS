using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class StackArgumentsRules
{
    /// <summary>按 AAPCS64 栈布局匹配到达写入，值在原写入位置快照；不把寄存器耗尽后的参数丢掉。</summary>
    [MachinePass("标量栈实参", 29, After = ["帧前类型"])]
    internal static void PrepareScalarStackArguments(this RecoveryScope ctx)
    {
        var definitions = ctx.values.Concat(ctx.function.Dead.Select(d => new KeyValuePair<Variable, Expr>(d.Define.Target, d.Define.Value))).GroupBy(p => p.Key).ToDictionary(g => g.Key, g => g.First().Value);
        Expr Definition(Expr expression, int depth = 12) => depth == 0 ? expression : ExprMap.Map(expression, e => e is Use use && definitions.TryGetValue(use.Variable, out var value) ? Definition(value, depth - 1) : null);
        long? Offset(Expr expression, HashSet<Variable> active) => expression switch
        {
            FrameAddress f => f.Offset,
            Binary { Op: BinOp.Add, Right: Const c } b when Offset(b.Left, active) is { } offset => offset + c.Signed,
            Binary { Op: BinOp.Sub, Right: Const c } b when Offset(b.Left, active) is { } offset => offset - c.Signed,
            Use u when active.Add(u.Variable) && definitions.TryGetValue(u.Variable, out var value) => Offset(value, active),
            _ => null,
        };
        var sp = ctx.owner.lifter.Machine.Convention.StackPointer;
        var writes = ctx.blocks.ToDictionary(b => b, b => b.Statements.OfType<Define>().Concat(ctx.function.Dead.Where(d => d.Block == b).Select(d => d.Define)).Where(d => d.Target.Storage == sp).DistinctBy(d => d.Target).OrderBy(d => d.Address).ToArray());
        var outputs = ctx.blocks.ToDictionary(b => b, _ => new HashSet<long?>());
        HashSet<long?> Input(Block block)
        {
            var input = block == ctx.function.EntryBlock ? new HashSet<long?>
            {
                0
            }

            : [];
            foreach (var parent in block.Predecessors.Where(outputs.ContainsKey))
                input.UnionWith(outputs[parent]);
            return input;
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var block in ctx.blocks)
            {
                var state = writes[block].LastOrDefault() is { } last ? new HashSet<long?>
                {
                    Offset(last.Value, [])
                }

                : Input(block);
                if (!outputs[block].SetEquals(state))
                {
                    outputs[block] = state;
                    changed = true;
                }
            }
        }
        while (changed);
        foreach (var block in ctx.blocks)
            foreach (var call in block.Statements.OfType<Call>().ToArray())
            {
                if (ctx.Resolve(call) is not { } callee || ctx.owner.abi.Classify(callee, out _) is not { } signature)
                    continue;
                var state = writes[block].LastOrDefault(d => d.Address < call.Address) is { } last ? new HashSet<long?>
                {
                    Offset(last.Value, [])
                }

                : Input(block);
                if (state.Count != 1 || state.Single() is not { } callSp)
                    continue;
                var layout = ctx.owner.abi.StackArguments(signature);
                ctx.State.Frames.callStackAreas[call.Address] = (callSp, layout.Size);
                // 一次向量写入可装载两个独立标量栈实参；按真实 ABI 槽拆分，继续使用原有快照规则。
                var scalarSlots = layout.Parameters.Where(p => !p.Indirect && ctx.types.Size(p.Type) is > 0 and <= 8
                    && ctx.types.Kind(p.Type) is TypeKind.Float or TypeKind.Double or TypeKind.Int or TypeKind.Bool or TypeKind.Reference)
                    .Select(p => p.Offset).ToHashSet();
                foreach (var offset in scalarSlots.Where(o => scalarSlots.Contains(o + 8)))
                {
                    if (ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + offset, [], 128) is not { Value: Use } wide
                        || ctx.State.Frames.stackArgumentStores.ContainsKey(wide) || !ctx.ExclusiveStackArgument(callSp + offset, 128)) continue;
                    var owner = ctx.blocks.Single(b => b.Statements.Contains(wide));
                    var at = owner.Statements.IndexOf(wide);
                    ctx.Rewriter.Replace(owner, at, new Store(wide.Address, new FrameAddress(callSp + offset), new Extract(wide.Value, 0, 64)));
                    ctx.InsertAnalysisStatement(owner, at + 1, new Store(wide.Address, new FrameAddress(callSp + offset + 8), new Extract(wide.Value, 64, 64)));
                }
                // 虚调用的隐藏 MethodInfo 与方法指针来自同一个 vtable 槽，寄存器耗尽时写入栈。
                if (call.Op?.Kind == OpKind.CallVirtual && layout.MethodInfoOffset is { } hidden && ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + hidden, []) is { } metadata && Definition(metadata.Value) is Load { Width: 64 } info && Definition(call.Target) is Load { Width: 64 } pointer && ctx.Split(info.Address) is var infoAt && ctx.Split(pointer.Address) is var pointerAt && infoAt.Base == pointerAt.Base && infoAt.Offset == pointerAt.Offset + 8)
                    ctx.State.Lowering.dropped.Add(metadata);
                foreach (var parameter in layout.Parameters)
                {
                    if (!parameter.Indirect && ctx.types.Kind(parameter.Type) == TypeKind.Struct && ctx.owner.abi.Hfa(parameter.Type) is { } hfa)
                    {
                        var leaves = ctx.StructPaths(parameter.Type).Where(p => ctx.types.Kind(p.Type) is TypeKind.Float or TypeKind.Double).ToArray();
                        var stores = leaves.Select(p => ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + parameter.Offset + p.Offset, [], hfa.Width)).ToArray();
                        if (leaves.Length != hfa.Count || stores.Any(s => s is null) || leaves.Any(p => !ctx.ExclusiveStackArgument(callSp + parameter.Offset + p.Offset, hfa.Width)) || stores.Where((s, i) => ctx.State.Frames.stackArgumentStores.TryGetValue(s!, out var local) && !local.Type.Equals(leaves[i].Type)).Any())
                            continue;
                        var parts = leaves.Select((p, i) =>
                        {
                            if (!ctx.State.Frames.stackArgumentStores.TryGetValue(stores[i]!, out var local))
                                ctx.State.Frames.stackArgumentStores[stores[i]!] = local = ctx.StructLocal(p.Type, hfa.Width);
                            return ((IReadOnlyList<FieldRef>)p.Path, (ManagedValue)local);
                        }).ToArray();
                        ctx.State.Frames.stackArgumentValues[(call.Address, parameter.Index)] = new ComposedValue(parameter.Type, parts);
                        continue;
                    }

                    if (ctx.types.Kind(parameter.Type) is not (TypeKind.Float or TypeKind.Double or TypeKind.Int or TypeKind.Bool or TypeKind.Reference))
                        continue;
                    var width = ctx.types.Size(parameter.Type) * 8;
                    if (width is not (8 or 16 or 32 or 64) || ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + parameter.Offset, [], width, allowWider: true) is not { } store)
                        continue;
                    // AAPCS64 栈参数按 8 字节对齐；整槽清零可用 64 位写入，参数只读取低位。
                    if (!ctx.ExclusiveStackArgument(callSp + parameter.Offset, store.Value.Width))
                        continue;
                    if (!ctx.State.Frames.stackArgumentStores.TryGetValue(store, out var local))
                        ctx.State.Frames.stackArgumentStores[store] = local = ctx.StructLocal(parameter.Type, width);
                    if (!local.Type.Equals(parameter.Type))
                        continue;
                    ctx.State.Frames.stackArgumentValues[(call.Address, parameter.Index)] = local;
                }
            }
    }

    internal static bool ExclusiveStackArgument(this RecoveryScope ctx, long offset, int width)
    {
        bool Exposes(Expr expression)
        {
            if (expression is Load)
                return false;
            if (ctx.FrameOffset(expression) is { } at)
                return at >= offset && at < offset + width / 8;
            return ExprMap.Children(expression).Any(Exposes);
        }

        // 消费写入前排除普通加载及地址逃逸，避免同一槽既是实参又是可变局部时丢失内存副作用。
        foreach (var statement in ctx.blocks.SelectMany(b => b.Statements))
        {
            var values = ExprMap.Operands(statement);
            foreach (var load in values.SelectMany(ExprMap.Walk).OfType<Load>())
                if (ctx.FrameOffset(load.Address) is { } at && at < offset + width / 8 && offset < at + load.Width / 8)
                    return false;
            var exposed = statement is Store store ? new[]
            {
                store.Value
            }

            : values;
            if (statement is Define { Value: Load } || statement is Define { Value: Ir.Convert { Operand: Load } })
                continue;
            if (exposed.Any(Exposes))
                return false;
        }

        return true;
    }

    [StoreRule(1)]
    internal static RecoveryResult<bool> StoreStackArgument(this LoweringScope ctx, Store store, List<ManagedStatement> output)
    {
        if (!ctx.State.Frames.stackArgumentStores.TryGetValue(store, out var local))
            return false;
        if (!ctx.Values.RecoverAs(store.Value, local.Type, store.Address).TryGet(out var value, out var failure))
            return failure;
        output.Add(new ManagedAssignment(store.Address, local, value));
        return true;
    }

    [ArgumentRule(1)]
    internal static ManagedValue? ScalarStackArgument(this LoweringScope ctx, AbiValue parameter, ArgumentSite site)
    {
        if (parameter.Passing != Passing.Stack)
            return null;
        return ctx.State.Frames.stackArgumentValues.GetValueOrDefault((site.Call.Address, site.Index));
    }
}
