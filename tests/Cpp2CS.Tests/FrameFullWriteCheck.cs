using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameFullWriteCheck
{
    [Command("frame-full-write", "连续栈写入的字段覆盖与生命期边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var first = new Store(0x1000, new FrameAddress(-32), Expr.C(0, 128));
        var last = new Store(0x1004, new FrameAddress(-16), Expr.C(0, 64));
        var value = new Variable(Storage.Gpr(0), 1);
        long? Offset(Expr expression) => expression is FrameAddress f ? f.Offset : null;
        Store? Start(params Stmt[] statements) => FrameCopySpans.FullWriteBefore(statements, statements.Length, -32, 24,
            [(0, 8), (8, 8), (16, 1)], Offset);
        a.True(ReferenceEquals(first, Start(first, last)), "128 + 64 位写入按真实字段覆盖证成完整新值");
        a.True(ReferenceEquals(last, Start(last, first)), "独立字段写入换序仍从实际首条开始");
        a.True(Start(first) is null, "只覆盖部分字段不能切断旧生命期");
        a.True(Start(first, new Define(0x1002, value, new Load(new FrameAddress(-24), 64)), last) is null,
            "两次写入间的读取阻止整组定义");
        a.True(ReferenceEquals(first, Start(first, new Define(0x1002, value, new Load(new FrameAddress(-64), 64)), last)),
            "不触及目标区域的读取保留原位置，不中断写入覆盖证明");
        a.True(Start(first, new Call(0x1002, CallKind.Direct, Expr.C(0x2000, 64)), last) is null,
            "不能跨调用把部分写入拼成整值");
        a.True(Start(first, new Store(0x1004, new FrameAddress(-16), Expr.C(0, 128))) is null,
            "越过已知结构体边界的写入仍拒绝");
        return a.Finish("frame-full-write");
    }
}
