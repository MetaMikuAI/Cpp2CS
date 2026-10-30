using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Machine.Algebra;

/// <summary>支配关系只依赖块编号与边；同一控制流快照内复用。</summary>
internal sealed class DominanceCache
{
    private (Block Block, int Index, Block[] Successors, Block[] Predecessors)[] graph = [];
    private Dominators? value;
    public Dominators Get(MachineFunction function)
    {
        if (value is not null && graph.Length == function.Blocks.Count && graph.Zip(function.Blocks).All(p =>
            ReferenceEquals(p.First.Block, p.Second) && p.First.Index == p.Second.Index
            && p.First.Successors.SequenceEqual(p.Second.Successors) && p.First.Predecessors.SequenceEqual(p.Second.Predecessors))) return value;
        graph = function.Blocks.Select(b => (b, b.Index, b.Successors.ToArray(), b.Predecessors.ToArray())).ToArray();
        return value = Dominators.Compute(function);
    }
}
