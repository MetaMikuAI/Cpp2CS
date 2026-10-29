using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FoldScaledIndexCheck
{
    [Command("fold-scaled-index", "窄整数的高位运算还原为缩放索引，保留溢出和符号", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var width in new[] { 32, 64 })
        foreach (var bits in new[] { 8, 16, 32 }.Where(b => b < width))
        foreach (var scale in new[] { 0, 1, 2, 3, 4 })
        foreach (var delta in new[] { 0UL, 1UL, ulong.MaxValue })
        {
            var up = width - bits;
            var shifted = new Binary(BinOp.Add, new Binary(BinOp.Shl, new Read(Storage.Gpr(0), width), Expr.C((ulong)up, width), width),
                Expr.C(delta << up, width), width);
            var original = new Binary(BinOp.AShr, shifted, Expr.C((ulong)(up - scale), width), width);
            var folded = Fold.Simplify(original);
            a.True(folded != original, "可证明的缩放索引被归约");
            foreach (var input in new[] { 0UL, 1UL, ulong.MaxValue, (1UL << (bits - 1)) - 1, 1UL << (bits - 1), 0x1234567887654321UL })
            {
                var evaluator = new Evaluator();
                evaluator.Registers[Storage.Gpr(0)] = input;
                a.Equal(evaluator.Eval(original), evaluator.Eval(folded), "最高位、负数与窄位溢出保持位型");
                a.True(evaluator.Failure is null, "原式与归约式可独立求值");
            }
        }
        var unaligned = new Binary(BinOp.AShr, new Binary(BinOp.Add,
            new Binary(BinOp.Shl, new Read(Storage.Gpr(0), 64), Expr.C(32, 64), 64), Expr.C(1, 64), 64), Expr.C(28, 64), 64);
        a.Equal<Expr>(unaligned, Fold.Simplify(unaligned), "低位不为零的偏移不套用窄整数加法");
        return a.Finish("fold-scaled-index");
    }
}
