using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>比较类初始化两臂的业务出口，空跳转不改变进入汇合块的值。</summary>
internal static class ClassGuardExits
{
    public static bool Same(Block first, ulong firstTarget, Block second, ulong secondTarget)
    {
        static (Block From, Block To)? Follow(Block from, ulong address)
        {
            var visited = new HashSet<Block> { from };
            var to = from.NormalSuccessors.FirstOrDefault(b => b.Start == address);
            while (to is not null && visited.Add(to))
            {
                if (to.Handler != from.Handler || to.IsLandingPad) return null;
                if (to.Statements.Where(s => s is not Nop).ToArray() is not [Jump jump]) return (from, to);
                if (to.NormalSuccessors.ToArray() is not [var next] || next.Start != jump.Target) return null;
                from = to; to = next;
            }
            return null;
        }
        if (first.Handler != second.Handler || Follow(first, firstTarget) is not { } left || Follow(second, secondTarget) is not { } right
            || left.To != right.To) return false;
        var a = left.To.Predecessors.IndexOf(left.From); var b = right.To.Predecessors.IndexOf(right.From);
        return a >= 0 && b >= 0 && left.To.Statements.OfType<Phi>().All(p => p.Sources.Length == left.To.Predecessors.Count && p.Sources[a] == p.Sources[b]);
    }
}
