using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Structure;

/// <summary>每遍索引值的传递使用点；区域查询只筛选使用点，不重新传播合流依赖。</summary>
internal sealed class StructureLiveness
{
    private readonly Dictionary<Term, HashSet<(BlockIdentity Block, bool End)>> users = [];

    public StructureLiveness(NativeFunction function, Func<Terminator, IEnumerable<Term>> endUses)
    {
        var merges = function.Blocks.SelectMany(b => b.Merges).ToDictionary(m => m.Result);
        foreach (var block in function.Blocks)
        {
            Add(block.Statements.SelectMany(SnapshotRewrite.Uses), (block.Identity, false));
            Add(endUses(block.End), (block.Identity, true));
        }
        void Add(IEnumerable<Term> roots, (BlockIdentity Block, bool End) point)
        {
            var pending = new Stack<Term>(roots);
            while (pending.TryPop(out var value))
            {
                if (!users.TryGetValue(value, out var points)) users[value] = points = [];
                if (!points.Add(point)) continue;
                foreach (var operand in value.Operands) pending.Push(operand);
                if (merges.TryGetValue(value, out var merge))
                    foreach (var input in merge.Inputs) pending.Push(input.Value);
            }
        }
    }

    public bool Outside(Term value, HashSet<BlockIdentity> inside, BlockIdentity head) =>
        users.TryGetValue(value, out var points) && points.Any(p => !inside.Contains(p.Block) && !(p.End && p.Block == head));
}
