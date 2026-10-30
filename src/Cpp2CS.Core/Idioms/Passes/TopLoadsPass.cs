using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class TopLoadsPass
{
    /// <summary>不在另一个读取的地址之内的读取。</summary>
    internal static IEnumerable<Load> TopLoads(Expr e)
    {
        if (e is Load load)
        {
            yield return load;
            yield break;
        }

        foreach (var child in ExprMap.Children(e))
            foreach (var l in TopLoadsPass.TopLoads(child))
                yield return l;
    }
}
