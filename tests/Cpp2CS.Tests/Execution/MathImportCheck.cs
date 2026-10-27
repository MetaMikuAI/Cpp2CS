using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Flow;
using Cpp2CS.Facts;
using Cpp2CS.Functions;

namespace Cpp2CS.Tests.Execution;

internal static class MathImportCheck
{
    [Command("math-import", "modf 与独立 C 数学库的位型对照", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var offset in new long[] { -8, -4, 0 })
        {
            var block = new Block(0x100) { Statements = [new Call(0x100, CallKind.Direct, Expr.C(0x200, 64))
            {
                Op = new(OpKind.Import, "modf"), Arguments = [new FrameAddress(offset), new Read(Storage.Vec(0), 128)],
                Sources = [], Results = [Storage.Vec(0)], Defines = [new Variable(Storage.Vec(0), 1)],
            }] };
            var function = new MachineFunction { Entry = block.Start, Range = new(0x100, 0x104, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
            var id = 1;
            a.Equal(offset == -8, MathImportNormalizer.Run(function, () => new(Storage.Temp(id++), 1)), "归一化后的导入参数及栈范围");
            if (offset == -8) a.True(block.Statements is [Define, Define, Store { Target: FrameAddress { Offset: -8 } }, Define], "整数写入与浮点返回均保留");
        }
        var input = new Read(Storage.Gpr(0), 64);
        var integral = new Unary(UnOp.FTrunc, input, 64);
        var fraction = MathImportNormalizer.Fraction(input, integral);
        ulong[] special = [0, 1UL << 63, 1, 0x8000000000000001, 0x0010000000000000, 0x000fffffffffffff,
            0x3ff0000000000000, 0xbff0000000000000, 0x3ff8000000000000, 0xbff8000000000000,
            0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000,
            0x7ff8000012345678, 0xfff8000012345678, 0x7ff0000012345678];
        var random = new Random(710);
        var inputs = special.Concat(Enumerable.Range(0, 128).Select(_ => unchecked((ulong)random.NextInt64())
            | (random.Next(2) == 0 ? 0UL : 1UL << 63)));
        foreach (var bits in inputs)
        {
            var value = BitConverter.Int64BitsToDouble(unchecked((long)bits));
            var expected = NativeMathLibrary.Modf(value, out var integer);
            var evaluator = new Evaluator();
            evaluator.Registers[Storage.Gpr(0)] = bits;
            Check(integer, (ulong)evaluator.Eval(integral), "整数部分");
            Check(expected, (ulong)evaluator.Eval(fraction), "小数部分");
            a.True(evaluator.Failure is null, "表达式可求值");
            void Check(double reference, ulong actual, string name)
            {
                if (double.IsNaN(reference)) a.True(double.IsNaN(BitConverter.Int64BitsToDouble(unchecked((long)actual))), name + " NaN");
                else a.Equal(unchecked((ulong)BitConverter.DoubleToInt64Bits(reference)), actual, $"{name} {bits:x16}");
            }
        }
        return a.Finish("math-import");
    }
}
