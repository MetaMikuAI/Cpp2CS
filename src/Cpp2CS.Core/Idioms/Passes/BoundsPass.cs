using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class BoundsPass
{
    /// <summary>越界条件拆成（索引, 长度）：idx ≥u len、idx >u len-1 等形式统一为两个操作数，原条件不能拆时保留条件本身。</summary>
    internal static Expr[] Bounds(Compare compare) => compare.Cond switch
    {
        Cond.Uge => [compare.Left, compare.Right],
        Cond.Ule => [compare.Right, compare.Left],
        _ => [compare],
    };
}
