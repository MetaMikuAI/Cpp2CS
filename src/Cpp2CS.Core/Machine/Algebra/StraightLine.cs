using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Machine.Algebra;

internal sealed record StraightLinePolicy(Func<Stmt?, bool> Continue, bool AllowLandingPad, bool NormalPredecessors)
{
    public static readonly StraightLinePolicy Jump = new(s => s is Ir.Jump, true, false);
    public static readonly StraightLinePolicy Fallthrough = new(s => s is not (Branch or Return or IndirectJump), false, false);
    public static readonly StraightLinePolicy Allocation = new(s => s is null or Ir.Jump or Call { Kind: CallKind.Direct or CallKind.Indirect }, false, true);
}

internal static class StraightLine
{
    public static IEnumerable<(Block Block, Stmt Statement)> Following(Block block, int index, StraightLinePolicy policy)
    {
        var visited = new HashSet<Block>();
        while (visited.Add(block))
        {
            for (var i = index + 1; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is Jump) break;
                yield return (block, block.Statements[i]);
            }
            if (!policy.Continue(block.Statements.LastOrDefault()) || block.NormalSuccessors.ToArray() is not [var next]) yield break;
            if (!policy.AllowLandingPad && next.IsLandingPad) yield break;
            var predecessors = policy.NormalPredecessors ? next.Predecessors.Count(p => p.NormalSuccessors.Contains(next)) : next.Predecessors.Count;
            if (predecessors != 1) yield break;
            block = next;
            index = -1;
        }
    }
}
