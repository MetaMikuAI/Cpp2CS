using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FoldZeroUnionCheck
{
    [Command("fold-zero-union", "按位或的零测试及读取顺序边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var left = new Use(new Variable(Storage.Gpr(0), 1), 64);
        var right = new Use(new Variable(Storage.Gpr(1), 1), 64);
        foreach (var cond in new[] { Cond.Eq, Cond.Ne })
        {
            var folded = Fold.Compare(cond, new Binary(BinOp.Or, left, right, 64), Expr.C(0, 64));
            a.True(folded is Logical, "寄存器快照转换为独立零测试");
            foreach (var pair in new[] { (0UL, 0UL), (0UL, 8UL), (8UL, 0UL), (8UL, 16UL), (ulong.MaxValue, 1UL) })
            {
                var value = Fold.Simplify(ExprMap.Map(folded, e => e == left ? Expr.C(pair.Item1, 64) : e == right ? Expr.C(pair.Item2, 64) : null));
                a.True(value is Const c && (c.Value != 0) == (((pair.Item1 | pair.Item2) == 0) == (cond == Cond.Eq)), "零、非零及不共享位的输入结果一致");
            }
            var load = new Load(right, 64);
            a.True(Fold.Compare(cond, new Binary(BinOp.Or, left, load, 64), Expr.C(0, 64)) is Compare,
                "不能短路有潜在异常的读取");
        }
        return a.Finish("fold-zero-union");
    }
}
