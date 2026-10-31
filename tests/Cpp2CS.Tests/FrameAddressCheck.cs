using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FrameAddressCheck
{
    [Command("frame-address", "栈地址低位按位或与对齐证明边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var offset in new long[] { -0xb0, -0xa8, -0xa4, 20 })
            foreach (var mask in new ulong[] { 4, 12 })
            {
                var folded = Fold.Binary(BinOp.Or, new FrameAddress(offset), Expr.C(mask, 64), 64);
                a.True(folded is FrameAddress, "低四位已知时可恢复帧地址");
                var actual = (FrameAddress)folded;
                a.Equal((0x1000UL + unchecked((ulong)offset)) | mask, 0x1000UL + unchecked((ulong)actual.Offset),
                    "包含已置位和负偏移时仍保留真实地址");
            }
        a.True(Fold.Binary(BinOp.Or, new FrameAddress(-0xa8), Expr.C(16, 64), 64) is Binary,
            "对齐不能证明第 4 位，保留原表达式");
        return a.Finish("frame-address");
    }
}
