using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FoldInsertCheck
{
    [Command("fold-insert", "常量位段合并及宽度边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        void Check(ulong basis, int width, ulong value, int bits, int low, ulong expected) =>
            a.Equal<Expr>(Expr.C(expected, width), Fold.Simplify(new Insert(Expr.C(basis, width), Expr.C(value, bits), low)),
                $"{width} 位常量的 [{low}, {low + bits}) 位替换");
        Check(0x5c00, 32, 0x526, 16, 16, 86400000);
        Check(0xaabbccdd, 32, 0x1234, 16, 0, 0xaabb1234);
        Check(0xaabbccdd, 32, 0, 8, 8, 0xaabb00dd);
        Check(0x0123456789abcdef, 64, 0xfedc, 16, 48, 0xfedc456789abcdef);
        Check(0, 64, 1, 1, 63, 0x8000000000000000);
        var nested = new Insert(new Insert(Expr.C(0xcdef, 64), Expr.C(0x89ab, 16), 16), Expr.C(0x01234567, 32), 32);
        a.Equal<Expr>(Expr.C(0x0123456789abcdef, 64), Fold.Simplify(nested), "连续分段构造常量");
        var unknown = new Insert(new Use(new(Storage.Gpr(0), 1), 64), Expr.C(7, 16), 16);
        a.Equal<Expr>(unknown, Fold.Simplify(unknown), "非常量保留原位段表达式");
        var vector = new Insert(Expr.C(0, 128), Expr.C(7, 64), 64);
        a.Equal<Expr>(vector, Fold.Simplify(vector), "高于 64 位的向量不截成 ulong 常量");
        foreach (var width in new[] { 32, 64 })
        foreach (var bits in new[] { 1, 8, 16, 32 })
        foreach (var low in new[] { 0, width - bits }.Distinct())
        {
            var insert = new Insert(new Read(Storage.Gpr(0), width), new Read(Storage.Gpr(1), bits), low);
            var scalar = Fold.ScalarInsert(insert)!;
            foreach (var basis in new[] { 0UL, ulong.MaxValue, 0x123456789abcdef0UL })
            foreach (var value in new[] { 0UL, ulong.MaxValue, 0xfedcba9876543210UL })
            {
                var evaluator = new Evaluator();
                evaluator.Registers[Storage.Gpr(0)] = basis;
                evaluator.Registers[Storage.Gpr(1)] = value;
                a.Equal(evaluator.Eval(insert), evaluator.Eval(scalar), "整数位段替换保留未写入的位");
                a.True(evaluator.Failure is null, "整数位段可求值");
            }
        }
        a.True(Fold.ScalarInsert(vector) is null, "向量不按整数打包");
        return a.Finish("fold-insert");
    }
}
