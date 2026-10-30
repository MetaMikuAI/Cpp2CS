using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DirectionPass
{
    /// <summary>代入 subst 之后条件的取值决定的分支方向：0 为跳转目标一侧，1 为顺序一侧；不确定为 null。</summary>
    internal static int? Direction(Expr condition, Func<Expr, Expr?> subst) => Fold.Simplify(ExprMap.Map(condition, subst)) is Const c ? (c.Value != 0 ? 0 : 1) : null;
}
