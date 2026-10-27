using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FoldCarryCheck
{
    [Command("fold-carry", "加法进位条件的无符号比较及回绕边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var width in new[] { 32, 64 })
        {
            var mask = Expr.Mask(width);
            var register = Storage.Gpr(0);
            foreach (var amount in new[] { 0UL, 1UL, 4UL, mask / 2, mask / 2 + 1, mask })
            foreach (var condition in new[] { FlagCondition.Hs, FlagCondition.Lo, FlagCondition.Hi, FlagCondition.Ls })
            {
                var expression = Fold.TestFlags(new Flags(FlagKind.Add, new Read(register, width), Expr.C(amount, width), width), condition);
                a.True(expression is not TestFlags, "进位条件已转换为普通表达式");
                var boundary = unchecked(0UL - amount) & mask;
                foreach (var value in new[] { 0UL, 1UL, mask, mask - 1, boundary, (boundary - 1) & mask, (boundary + 1) & mask }.Distinct())
                {
                    var sum = (UInt128)value + amount;
                    var carry = sum > mask;
                    var zero = (sum & mask) == 0;
                    var expected = condition switch { FlagCondition.Hs => carry, FlagCondition.Lo => !carry, FlagCondition.Hi => carry && !zero, _ => !carry || zero };
                    var evaluator = new Evaluator();
                    evaluator.Registers[register] = value;
                    a.Equal<UInt128>(expected ? 1u : 0u, evaluator.Eval(expression), $"{width} 位 {value}+{amount} 的 {condition}");
                    a.True(evaluator.Failure is null, "转换后表达式可求值");
                }
            }
        }
        return a.Finish("fold-carry");
    }
}
