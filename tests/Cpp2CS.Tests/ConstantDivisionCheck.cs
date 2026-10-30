using System.Numerics;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class ConstantDivisionCheck
{
    [Command("constant-division", "乘高位常量除法的舍入边界与拒绝条件", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var input = new Use(new(Storage.Gpr(0), 0), 64);
        var high = new Variable(Storage.Gpr(1), 1);
        var shifted = new Variable(Storage.Gpr(2), 1);
        var adjusted = new Variable(Storage.Gpr(3), 1);
        MachineFunction Function(ulong magic, int shift, int signShift = 63, BinOp multiply = BinOp.MulHighS, bool compensate = false) => new()
        {
            Entry = 0, Range = new(0, 16, CodeRegion.Managed, BoundaryEvidence.EhFrame),
            Blocks = [new(0) { Statements =
            [
                new Define(0, high, new Binary(multiply, input, Expr.C(magic, 64), 64)),
                new Define(4, adjusted, compensate ? new Binary(BinOp.Add, new Use(high, 64), input, 64) : new Use(high, 64)),
                new Define(8, shifted, new Binary(BinOp.AShr, new Use(adjusted, 64), Expr.C((ulong)shift, 64), 64)),
                new Return(8) { Value = new Binary(BinOp.Add, new Use(shifted, 64),
                    new Binary(BinOp.LShr, new Use(adjusted, 64), Expr.C((ulong)signShift, 64), 64), 64) },
            ] }],
        };
        var random = new Random(731);
        foreach (var divisor in new long[] { 3, 5, 7, 9, 10, 12, 60, 1000, 86400, 10000000 })
        {
            var accepted = false;
            for (var shift = 0; shift < 32 && !accepted; shift++)
            {
                var scale = BigInteger.One << (64 + shift);
                var multiplier = (scale + divisor - 1) / divisor;
                if (multiplier > ulong.MaxValue) break;
                var compensate = multiplier > long.MaxValue;
                var function = Function((ulong)multiplier, shift, compensate: compensate);
                if (!ConstantDivisionNormalizer.Run(function)) continue;
                accepted = true;
                a.True(function.EntryBlock.Statements[^1] is Return
                    { Value: Binary { Op: BinOp.SDiv, Right: Const constant } } && constant.Value == (ulong)divisor,
                    "除数由乘数和移位还原");
                var edge = long.MaxValue / divisor * divisor;
                var inputs = new List<long> { long.MinValue, long.MinValue + 1, long.MaxValue, -edge - 1, -edge, -edge + 1,
                    edge - 1, edge, edge + 1, -divisor - 1, -divisor, -divisor + 1, -1, 0, 1, divisor - 1, divisor, divisor + 1 };
                inputs.AddRange(Enumerable.Range(0, 256).Select(_ => random.NextInt64(long.MinValue, long.MaxValue)));
                foreach (var value in inputs)
                {
                    var signedMultiplier = compensate ? multiplier - (BigInteger.One << 64) : multiplier;
                    var productHigh = (new BigInteger(value) * signedMultiplier) >> 64;
                    if (compensate) productHigh += value;
                    var native = (productHigh >> shift) + (productHigh.Sign < 0 ? 1 : 0);
                    a.True(native == new BigInteger(value) / divisor, "无限精度对照极值、负数与整倍数相邻值");
                }
            }
            a.True(accepted, "常量除法存在可证明的乘高位形式");
        }
        a.True(!ConstantDivisionNormalizer.Run(Function(1UL << 62, 0)), "精确倒数缺少正确的负数修正");
        a.True(!ConstantDivisionNormalizer.Run(Function(0x5555555555555557, 0)), "拒绝超出全输入误差界的近似乘数");
        a.True(!ConstantDivisionNormalizer.Run(Function(0x5555555555555556, 0, 62)), "拒绝错误的符号位位置");
        a.True(!ConstantDivisionNormalizer.Run(Function(0x5555555555555556, 0, multiply: BinOp.MulHighU)), "无符号乘高位不能套用有符号证明");
        a.True(!ConstantDivisionNormalizer.Run(Function(0x8888888888888889, 5)), "负乘数缺少加回原输入时不能恢复除法");
        a.True(!ConstantDivisionNormalizer.Run(Function(0x5555555555555556, 0, compensate: true)), "正乘数不能额外加回输入");
        var wrongInput = Function(0x8888888888888889, 5, compensate: true);
        wrongInput.EntryBlock.Statements[1] = new Define(4, adjusted,
            new Binary(BinOp.Add, new Use(high, 64), new Use(new(Storage.Gpr(4), 0), 64), 64));
        a.True(!ConstantDivisionNormalizer.Run(wrongInput), "补偿项必须是原被除数");
        var wrongSign = Function(0x8888888888888889, 5, compensate: true);
        wrongSign.EntryBlock.Statements[^1] = new Return(8) { Value = new Binary(BinOp.Add, new Use(shifted, 64),
            new Binary(BinOp.LShr, new Use(high, 64), Expr.C(63, 64), 64), 64) };
        a.True(!ConstantDivisionNormalizer.Run(wrongSign), "负乘数的符号修正必须来自补偿后的乘积");
        var unrelated = Function(0x5555555555555556, 0);
        unrelated.EntryBlock.Statements[^1] = new Return(8) { Value = new Binary(BinOp.Add, new Use(shifted, 64),
            new Binary(BinOp.LShr, new Use(new(Storage.Gpr(3), 0), 64), Expr.C(63, 64), 64), 64) };
        a.True(!ConstantDivisionNormalizer.Run(unrelated), "符号修正必须来自同一个乘积");
        return a.Finish("constant-division");
    }
}
