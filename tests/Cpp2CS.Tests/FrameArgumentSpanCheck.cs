using Cpp2CS.Recovery;
using Cpp2CS.Ir;
using Cpp2CS.Facts;

namespace Cpp2CS.Tests;

internal static class FrameArgumentSpanCheck
{
    [Command("frame-argument-span", "寄存器实参与返回片的完整栈范围", Gate = Gate.Unit)]
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
        var second = new Variable(Storage.Gpr(0), 1);
        definitions[second] = new Define(0x108, second, new Load(new FrameAddress(-24), 64));
        AbiPiece[] abi = [new(Storage.Gpr(0), 64, 0), new(Storage.Gpr(1), 64, 8)];
        var returned = new Intrinsic("diagnostic_return", [new Use(copy, 64), new Use(second, 64)], 64);
        (long Origin, Define[] Reads)? ReturnSpan(Expr value) => FrameArgumentSpan.ReturnLoads(value, abi, 16, definitions,
            e => e is FrameAddress frame ? frame.Offset : null);
        a.True(ReturnSpan(returned) is { Origin: -32, Reads.Length: 2 } span && span.Reads[0] == definition,
            "返回签名沿副本保留完整栈区域与真实读取点");
        a.True(ReturnSpan(new Intrinsic("diagnostic_return", [new Use(second, 64), new Use(copy, 64)], 64)) is null,
            "交换返回寄存器不能错认同一结构体");
        a.True(ReturnSpan(new Use(copy, 64)) is null, "缺少返回寄存器不提供完整布局");
        a.True(ReturnSpan(new Intrinsic("diagnostic_return", [new Use(copy, 64), Expr.C(0, 64)], 64)) is null,
            "常量返回片不冒充栈读取证据");
        definitions[first] = new Define(0x100, first, new Use(copy, 64));
        a.True(FrameArgumentSpan.Loaded(new Use(copy, 64), definitions) is null, "循环定义没有栈证据");
        return a.Finish("frame-argument-span");
    }
}
