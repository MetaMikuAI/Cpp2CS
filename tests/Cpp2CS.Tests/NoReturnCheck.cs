using Cpp2CS.Arm64;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class NoReturnCheck
{
    [Command("no-return-empty", "无效果指令之后的返回、陷阱和函数边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        const uint discard = 0xAA0003FF; // mov xzr, x0
        var statements = new List<Stmt>();
        Arm64Lifter.Lift(0x1000, discard, statements);
        a.Equal(0, statements.Count, "写入零寄存器不产生 IR");
        bool Returns(params uint[] words) => new NoReturnOracle(new Machine(words), null!).Returns(0x1000,
            new(0x1000, 0x1000 + (ulong)words.Length * 4, CodeRegion.Runtime, default));
        a.True(Returns(discard, 0xD65F03C0), "无效果指令后 ret 仍可返回");
        a.True(!Returns(discard, 0xD4200000), "无效果指令后 brk 不返回");
        a.True(Returns(discard), "顺序越过函数边界保持会返回的保守判定");
        return a.Finish("no-return-empty");
    }

    private sealed class Machine(uint[] words) : IMachine
    {
        public Architecture Architecture => Architecture.Arm64;
        public ImageDocument Image => throw new NotSupportedException();
        public CallingConvention Convention => throw new NotSupportedException();
        public int Lift(ulong address, List<Stmt> output)
        {
            var index = checked((int)((address - 0x1000) / 4));
            if (index >= words.Length) return 0;
            Arm64Lifter.Lift(address, words[index], output);
            return 4;
        }
    }
}
