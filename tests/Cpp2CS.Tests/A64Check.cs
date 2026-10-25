using Cpp2CS.Facts;

namespace Cpp2CS.Tests;

/// <summary>
/// <see cref="A64"/> 解码的单元测试。用固定指令字和人工地址验证字段、符号偏移与边界距离。
/// </summary>
internal static class A64Check
{
    [Command("a64", "ARM64 指令字段与地址计算检查", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();

        // bl -0x100；b +0x80。
        a.True(A64.IsBl(0x97FFFFC0u), "bl 识别");
        a.Equal(0x1F00UL, A64.Imm26Target(0x97FFFFC0u, 0x2000), "bl 目标（向后）");
        a.True(A64.IsB(0x14000020u) && !A64.IsBl(0x14000020u), "b 识别");
        a.Equal(0x2080UL, A64.Imm26Target(0x14000020u, 0x2000), "b 目标（向前）");
        // 手工：bl -4（imm26 全 1）；b 最远正向 +0x7FFFFFC
        a.Equal(0xFFCUL, A64.Imm26Target(0x97FFFFFFu, 0x1000), "bl 负一条");
        a.Equal(0x1000UL + 0x7FFFFFC, A64.Imm26Target(0x15FFFFFFu, 0x1000), "b 最远正向");

        // cbnz w8, +12；cbz w8, +12；tbnz w8, #4, +12。
        a.Equal(0x100CUL, A64.ConditionalTarget(0x35000068u, 0x1000), "cbnz 目标");
        a.Equal(0x100CUL, A64.ConditionalTarget(0x34000068u, 0x1000), "cbz 目标");
        a.Equal(0x100CUL, A64.ConditionalTarget(0x37200068u, 0x1000), "tbnz 目标");
        a.Equal(8, A64.Rd(0x34000068u), "cbz 测试寄存器");
        // 手工：b.ne -8（imm19 = -2，cond = 1）；tbnz w8, #5, -4（imm14 全 1）
        a.Equal(0xFF8UL, A64.ConditionalTarget(0x54FFFFC1u, 0x1000), "b.ne 负向");
        a.Equal(0xFFCUL, A64.ConditionalTarget(0x372FFFE8u, 0x1000), "tbnz 负向");
        a.Equal(null, A64.ConditionalTarget(0x140000C6u, 0), "无条件 b 不是条件分支");

        // adrp x1, -1 页；adrp x1, +1 页；add x1, x1, #0xa0d。
        a.True(A64.IsAdrp(0xF0FFFFE1u), "adrp 识别");
        a.Equal(0x1000UL, A64.AdrpPage(0xF0FFFFE1u, 0x2345), "adrp 负向页");
        a.Equal(0x3000UL, A64.AdrpPage(0xB0000001u, 0x2345), "adrp 正向页");
        a.Equal(1, A64.Rd(0xF0FFFFE1u), "adrp 目的寄存器");
        a.True(A64.IsAddImmediate64(0x91283421u), "add 立即数识别");
        a.Equal(0xa0dUL, A64.AddImmediate(0x91283421u), "add 立即数");
        a.Equal(1, A64.Rn(0x91283421u), "add 基址寄存器");

        // ldr x1, [x1, #0x900]；ldrb w8, [x22, #0x132]；ldrh w8, [x1, #0x4c]；str x19, [x0]
        a.True(A64.IsUnsignedOffsetAccess(0xF9448021u) && !A64.IsStore(0xF9448021u), "ldr x 识别为读");
        a.Equal(8, A64.AccessSize(0xF9448021u), "ldr x 宽度");
        a.Equal(0x900UL, A64.AccessOffset(0xF9448021u), "ldr x 偏移");
        a.Equal((1, 0x132UL), (A64.AccessSize(0x3944CAC8u), A64.AccessOffset(0x3944CAC8u)), "ldrb 宽度与偏移");
        a.Equal(22, A64.Rn(0x3944CAC8u), "ldrb 基址");
        a.Equal((2, 0x4cUL), (A64.AccessSize(0x79409828u), A64.AccessOffset(0x79409828u)), "ldrh 宽度与偏移");
        a.True(A64.IsStore(0xF9000013u), "str 识别为写");
        a.True(!A64.MayWriteRd(0xF9000013u), "str 不写 Rt");
        a.True(A64.MayWriteRd(0xF9448021u), "ldr 写 Rt");

        // blr x8；ret；dmb ish；ubfx x8, x0, #0x1d, #3；ldaxr 不是无符号偏移访存
        a.True(A64.IsBlr(0xD63F0100u) && A64.Rn(0xD63F0100u) == 8, "blr x8");
        a.True(A64.IsRet(0xD65F03C0u), "ret");
        a.True(!A64.MayWriteRd(0xD5033BBFu), "dmb 不写寄存器");
        a.True((0xD35D7C08u & 0xFFFFFC00) == 0xD35D7C00, "ubfx #29,#3 模式");
        a.True(!A64.IsUnsignedOffsetAccess(0xC85FFC08u), "ldaxr 不按无符号偏移访存处理");
        a.True(!A64.IsUnsignedOffsetAccess(0xA9400408u), "ldp 不按无符号偏移访存处理");

        return a.Finish("a64");
    }
}
