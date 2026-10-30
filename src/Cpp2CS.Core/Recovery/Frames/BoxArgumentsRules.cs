using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class BoxArgumentsRules
{
    /// <summary>标量写进临时栈槽后跨块装箱：在原写入处保存值，不把栈地址当托管值。</summary>
    [MachinePass("汇合装箱", 23, After = ["标量栈实参"])]
    internal static void PrepareMergedBoxArguments(this RecoveryScope ctx)
    {
        var changed = false;
        foreach (var block in ctx.blocks)
            foreach (var call in block.Statements.OfType<Call>().ToArray())
            {
                if (call is not { Op: { Kind: OpKind.Box, Operand: TypeRef type }, Arguments: [_, var data] } || ctx.types.Kind(type) is not (TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double))
                    continue;
                var width = ctx.types.Size(type) * 8;
                Store?[] sources;
                if (ctx.FrameOffset(data) is { } directOffset)
                    sources = [ctx.ReachingStackStore(block, block.Statements.IndexOf(call), directOffset, [], width)];
                else if (data is Use pointer && ctx.phis.TryGetValue(pointer.Variable, out var phi) && block.Statements.Contains(phi) && phi.Sources.Length == block.Predecessors.Count)
                {
                    if (block.Statements.Take(block.Statements.IndexOf(call)).Any(s => s is Store or Call))
                        continue;
                    if (ctx.blocks.SelectMany(b => b.Statements).Where(s => s != call && s != phi).Any(s => s is Phi other && other.Sources.Contains(phi.Target) || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == phi.Target)))
                        continue;
                    sources = phi.Sources.Select((source, i) => ctx.FrameOffset(new Use(source, 64)) is { } offset ? ctx.ReachingStackStore(block.Predecessors[i], block.Predecessors[i].Statements.Count, offset, [], width) : null).ToArray();
                }
                else
                    continue;
                if (sources.Any(s => s is null || ctx.State.Construction.boxArgumentStores.ContainsKey(s)))
                    continue;
                // 栈槽只能由这些写入和地址定义访问；普通加载或其他调用继续交给帧区域恢复。
                var offsets = sources.Select(s => ctx.FrameOffset(s!.Target)!.Value).ToHashSet();
                if (ctx.blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>().Any(load => ctx.FrameOffset(load.Address) is { } at && offsets.Any(offset => at < offset + width / 8 && offset < at + load.Width / 8)))
                    continue;
                if (ctx.blocks.SelectMany(b => b.Statements).Where(s => s != call && s is not (Define or Phi) && !sources.Contains(s)).SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Any(e => ctx.FrameOffset(e) is { } offset && offsets.Contains(offset)))
                    continue;
                var local = ctx.StructLocal(type, width);
                foreach (var store in sources)
                    ctx.State.Construction.boxArgumentStores[store!] = local;
                ctx.State.Construction.mergedBoxValues[call.Address] = local;
                var replacement = call with
                {
                    Arguments = [call.Arguments[0], Expr.C(0, 64)]
                };
                ctx.Rewriter.Replace(block, block.Statements.IndexOf(call), replacement);
                ctx.Rewriter.Preserve(call, replacement);
                changed = true;
            }

        if (!changed)
            return;
        ctx.RemoveDeadDefinitions();
        ctx.definitions = ctx.IndexDefinitions();
    }

    [StoreRule(2)]
    internal static RecoveryResult<bool> StoreBoxArgument(this LoweringScope ctx, Store store, List<ManagedStatement> output)
    {
        if (!ctx.State.Construction.boxArgumentStores.TryGetValue(store, out var local))
            return false;
        if (!ctx.Values.RecoverAs(store.Value, local.Type, store.Address).TryGet(out var value, out var failure))
            return failure;
        output.Add(new ManagedAssignment(store.Address, local, value));
        return true;
    }

    [CallRule(9)]
    internal static RecoveryResult<bool> BoxMergedArgument(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (!ctx.State.Construction.mergedBoxValues.TryGetValue(call.Address, out var local) || call.Defines.FirstOrDefault() is not { } result)
            return false;
        if (ctx.Values.Assign(call.Address, result, () => new BoxValue(local, local.Type, ctx.types.Object), output) is { } failure)
            return failure;
        return true;
    }
}
