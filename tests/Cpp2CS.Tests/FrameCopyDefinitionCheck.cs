using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameCopyDefinitionCheck
{
    [Command("frame-copy-definition", "完整栈复制的生命期边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var low = new Store(0x100, new FrameAddress(-64), new Use(new(Storage.Vec(0), 1), 128));
        var high = new Store(0x104, new FrameAddress(-48), new Use(new(Storage.Vec(1), 1), 128));
        a.True(ReferenceEquals(low, FrameCopySpans.WriteStart([low, high], [high, low])), "以语句顺序确定起点");
        a.True(ReferenceEquals(high, FrameCopySpans.WriteStart([high, low], [low, high])), "高片先写也保留真实顺序");
        a.True(FrameCopySpans.WriteStart([low], [low, high]) is null, "缺失写入不能定义整值");
        a.True(FrameCopySpans.WriteStart([low, high], []) is null, "没有写入证据");
        Stmt[] barriers = [
            new Define(0x102, new(Storage.Gpr(0), 1), new Load(new FrameAddress(-64), 64)),
            new Call(0x102, CallKind.Direct, Expr.C(0x200, 64)),
            new Store(0x102, new FrameAddress(-56), Expr.C(0, 64))];
        foreach (var barrier in barriers)
            a.True(FrameCopySpans.WriteStart([low, barrier, high], [low, high]) is null, $"不跨越 {barrier.GetType().Name}");
        return a.Finish("frame-copy-definition");
    }
}
