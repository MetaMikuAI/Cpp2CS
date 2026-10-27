using Cpp2CS.Recovery;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FrameArgumentSpanCheck
{
    [Command("frame-argument-span", "寄存器实参片的完整栈范围", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        a.Equal<long?>(-32, FrameArgumentSpan.Origin(16, [(0, 64, -32), (8, 64, -24)]), "完整相邻整数片");
        a.Equal<long?>(-32, FrameArgumentSpan.Origin(16, [(8, 32, -24), (0, 32, -32), (12, 32, -20), (4, 32, -28)]), "浮点片按 ABI 偏移核对");
        a.True(FrameArgumentSpan.Origin(16, [(0, 64, -32)]) is null, "缺失片不能定型");
        a.True(FrameArgumentSpan.Origin(16, [(0, 64, -24), (8, 64, -32)]) is null, "次序错位不能拼接");
        a.True(FrameArgumentSpan.Origin(16, [(0, 64, -32), (0, 64, -32)]) is null, "重叠片不能冒充完整覆盖");
        a.True(FrameArgumentSpan.Origin(12, [(0, 64, -32), (8, 64, -24)]) is null, "读取超出完整类型的范围不能定型");
        a.True(FrameArgumentSpan.Origin(16, [(0, 64, -8), (8, 64, 0)]) is null, "调用者栈不作为局部区域");
        var first = new Variable(Storage.Gpr(1), 1);
        var copy = new Variable(Storage.Gpr(2), 1);
        var definition = new Define(0x100, first, new Load(new FrameAddress(-32), 64));
        var definitions = new Dictionary<Variable, Define>
        {
            [first] = definition,
            [copy] = new Define(0x104, copy, new Use(first, 64)),
        };
        a.True(FrameArgumentSpan.Loaded(new Use(copy, 64), definitions)?.Statement == definition, "等宽 SSA 副本追到真实读取点");
        a.True(FrameArgumentSpan.Loaded(new Use(copy, 32), definitions) is null, "截断使用不冒充整片读取");
        definitions[first] = new Define(0x100, first, new Use(copy, 64));
        a.True(FrameArgumentSpan.Loaded(new Use(copy, 64), definitions) is null, "循环定义没有栈证据");
        return a.Finish("frame-argument-span");
    }
}
