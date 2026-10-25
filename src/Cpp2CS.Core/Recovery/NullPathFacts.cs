using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>完整寄存器判零的分支事实；只传播不可变 SSA 值，不传播可重新加载的字段。</summary>
internal sealed class NullPathFacts
{
    private readonly Dominators dominators;
    private readonly Dictionary<ulong, Block[]> locations;
    private readonly List<(Use Value, Block Block)> zeros = [];

    public NullPathFacts(MachineFunction function)
    {
        dominators = Dominators.Compute(function);
        locations = function.Blocks.SelectMany(b => b.Statements.Select(s => (s.Address, Block: b)))
            .GroupBy(p => p.Address).ToDictionary(g => g.Key, g => g.Select(p => p.Block).Distinct().ToArray());
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Compare test } branch
                || test.Cond is not (Cond.Eq or Cond.Ne) || branch.Target == branch.Fallthrough) continue;
            var value = test switch
            {
                { Left: Use { Width: 64 } use, Right: Const { Value: 0, Width: 64 } } => use,
                { Right: Use { Width: 64 } use, Left: Const { Value: 0, Width: 64 } } => use,
                _ => null,
            };
            if (value is null) continue;
            var target = test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough;
            var zero = block.NormalSuccessors.SingleOrDefault(b => b.Start == target);
            // 分支目标有其他入口时，不能用其中一条边的条件代表整个块。
            if (zero is not null && zero.Predecessors.Count == 1 && zero.Predecessors[0] == block)
                zeros.Add((value, zero));
        }
    }

    public bool IsNull(Expr value, ulong address) => value is Use { Width: 64 }
        && locations.TryGetValue(address, out var uses) && uses is [var use]
        && zeros.Any(z => z.Value == value && dominators.Dominates(z.Block.Index, use.Index));
}
