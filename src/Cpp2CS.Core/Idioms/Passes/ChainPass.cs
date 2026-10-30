using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

internal static class ChainPass
{
    /// <summary>从 start 出发的单前驱、单后继直链，直到 merge；不是直链返回 null。</summary>
    internal static List<Block>? Chain(Block start, Block merge)
    {
        var chain = new List<Block>();
        for (var b = start; b != merge;)
        {
            if (b.Predecessors.Count != 1 || b.IsLandingPad || chain.Count >= 64)
                return null;
            var next = b.NormalSuccessors.ToArray();
            if (next.Length != 1)
                return null;
            chain.Add(b);
            b = next[0];
        }

        return chain;
    }
}
