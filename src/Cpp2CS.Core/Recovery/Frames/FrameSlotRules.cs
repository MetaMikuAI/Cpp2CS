using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class FrameSlotRules
{
    /// <summary>栈帧：序言保存的被调用者保存寄存器删去；只被写入一次再装箱的栈槽并入装箱。其余栈访问为洞。</summary>
    [MachinePass("帧槽", 60, After = ["帧区域", "栈上调用"])]
    internal static void FrameSlots(this RecoveryScope ctx)
    {
        var callFrames = new ManagedCallFrames(ctx.facts, ctx.owner.abi);
        var deadWrites = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var references = new Dictionary<long, List<Stmt>>();
        foreach (var block in ctx.blocks)
            foreach (var statement in block.Statements)
                if (!ctx.State.Lowering.dropped.Contains(statement) && (statement is not Call enumCall || !ctx.State.Frames.stackEnums.ContainsKey(enumCall)) && (statement is not Store savedArgument || !ctx.State.Frames.stackArgumentStores.ContainsKey(savedArgument) && !ctx.State.Construction.boxArgumentStores.ContainsKey(savedArgument)))
                    foreach (var e in ExprMap.Operands(statement).SelectMany(ExprMap.Walk))
                        if (e is FrameAddress frame)
                        {
                            if (!references.TryGetValue(frame.Offset, out var list))
                                references[frame.Offset] = list = [];
                            list.Add(statement);
                        }

        foreach (var (offset, users) in references)
        {
            var distinct = users.Distinct(ReferenceEqualityComparer.Instance).Cast<Stmt>().ToArray();
            if (distinct.All(s => s is Store { Target: FrameAddress at, Value: Use or Const } && at.Offset == offset) && distinct.Cast<Store>().All(store => FrameWritebacks.Unread(ctx.blocks.SelectMany(b => b.Statements).Where(s => !ctx.State.Lowering.dropped.Contains(s)), store, callFrames.ArgumentSize, ctx.NoStackRead)))
            {
                ctx.State.Lowering.dropped.UnionWith(distinct);
                deadWrites.UnionWith(distinct);
                continue;
            }

            if (distinct is [Store { Target: FrameAddress, Value: Use { Variable: { Version: 0 } saved } } spill] && MethodRecovery.CalleeSaved.Concat([Storage.Gpr(29), Storage.Gpr(30)]).Contains(saved.Storage))
            {
                ctx.State.Lowering.dropped.Add(spill);
                continue;
            }

            if (distinct is [Store { Target: FrameAddress } store, Call { Op.Kind: OpKind.Box } box] && box.Arguments is [_, FrameAddress] && ctx.SameBlockBefore(store, box))
            {
                ctx.State.Lowering.dropped.Add(store);
                ctx.State.Construction.boxed[box] = store.Value;
                continue;
            }

            var hole = ctx.Hole(distinct[0].Address, ctx.State.Frames.conflictingFrames.Contains(offset) ? $"栈 栈槽类型冲突 {offset:x}" : $"栈 栈槽 {offset:x} 的使用形态尚未支持", rule: "FrameSlots");
            ctx.State.Frames.frameHoles[offset] = hole;
            foreach (var user in distinct)
            {
                ctx.ledger.Block(user, hole);
            }
        }

        if (deadWrites.Count > 0)
        {
            foreach (var block in ctx.blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    if (deadWrites.Contains(block.Statements[i]))
                        ctx.Rewriter.Replace(block, i, new Nop(block.Statements[i].Address, "未读取的栈快照"));
            ctx.RemoveDeadDefinitions();
            ctx.definitions = ctx.IndexDefinitions();
        }
    }
}
