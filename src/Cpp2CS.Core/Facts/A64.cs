
namespace Cpp2CS.Facts;

/// <summary>
/// 事实层只需要的 AArch64 指令字解码：分支、PC 相对寻址、立即数加法与无符号偏移访存。
/// 只按编码位精确匹配，不做语义提升；位域依据 Arm ARM（DDI 0487）A64 编码表。
/// </summary>
public static class A64
{
    public const uint Nop = 0xD503201F;

    public static bool IsBl(uint w) => (w & 0xFC000000) == 0x94000000;
    public static bool IsB(uint w) => (w & 0xFC000000) == 0x14000000;

    /// <summary>B / BL：imm26 × 4，有符号。</summary>
    public static ulong Imm26Target(uint w, ulong pc) => unchecked(pc + (ulong)(((long)((ulong)(w & 0x03FFFFFF) << 38)) >> 36));

    public static bool IsBCond(uint w) => (w & 0xFF000010) == 0x54000000;
    public static bool IsCbz(uint w) => (w & 0x7E000000) == 0x34000000;
    public static bool IsTbz(uint w) => (w & 0x7E000000) == 0x36000000;

    /// <summary>B.cond / CBZ / CBNZ：imm19 × 4，有符号。</summary>
    public static ulong Imm19Target(uint w, ulong pc) => unchecked(pc + (ulong)(((long)((ulong)((w >> 5) & 0x7FFFF) << 45)) >> 43));

    /// <summary>TBZ / TBNZ：imm14 × 4，有符号。</summary>
    public static ulong Imm14Target(uint w, ulong pc) => unchecked(pc + (ulong)(((long)((ulong)((w >> 5) & 0x3FFF) << 50)) >> 48));

    /// <summary>条件分支（B.cond、CBZ/CBNZ、TBZ/TBNZ）的目标；不是条件分支返回 null。</summary>
    public static ulong? ConditionalTarget(uint w, ulong pc) =>
        IsBCond(w) || IsCbz(w) ? Imm19Target(w, pc) : IsTbz(w) ? Imm14Target(w, pc) : null;

    public static bool IsBlr(uint w) => (w & 0xFFFFFC1F) == 0xD63F0000;
    public static bool IsBr(uint w) => (w & 0xFFFFFC1F) == 0xD61F0000;
    public static bool IsRet(uint w) => (w & 0xFFFFFC1F) == 0xD65F0000 || w is 0xD65F0BFF or 0xD65F0FFF;

    /// <summary>BRK / UDF：陷阱或填充。</summary>
    public static bool IsTrap(uint w) => (w & 0xFFE0001F) == 0xD4200000 || (w & 0xFFFF0000) == 0;

    public static bool IsAdrp(uint w) => (w & 0x9F000000) == 0x90000000;
    public static bool IsAdr(uint w) => (w & 0x9F000000) == 0x10000000;

    private static long AdrImmediate(uint w) => ((long)((ulong)((((w >> 5) & 0x7FFFF) << 2) | ((w >> 29) & 3)) << 43)) >> 43;

    public static ulong AdrpPage(uint w, ulong pc) => unchecked((pc & ~0xFFFUL) + (ulong)(AdrImmediate(w) << 12));
    public static ulong AdrTarget(uint w, ulong pc) => unchecked(pc + (ulong)AdrImmediate(w));

    public static int Rd(uint w) => (int)(w & 31);
    public static int Rn(uint w) => (int)((w >> 5) & 31);

    /// <summary>ADD Xd, Xn, #imm{, LSL #12}（64 位、不设标志）。</summary>
    public static bool IsAddImmediate64(uint w) => (w & 0xFF800000) == 0x91000000;

    public static ulong AddImmediate(uint w) => ((w >> 10) & 0xFFF) << (((w >> 22) & 1) != 0 ? 12 : 0);

    /// <summary>LDR/STR（无符号立即数偏移），含 SIMD/FP 寄存器形式。</summary>
    public static bool IsUnsignedOffsetAccess(uint w) => (w & 0x3B000000) == 0x39000000;

    /// <summary>无符号偏移访存的访问宽度（字节）。</summary>
    public static int AccessSize(uint w)
    {
        var size = (int)(w >> 30);
        var vector = ((w >> 26) & 1) != 0;
        var opc = (w >> 22) & 3;
        return vector && size == 0 && opc >= 2 ? 16 : 1 << size;
    }

    public static ulong AccessOffset(uint w) => ((w >> 10) & 0xFFF) * (ulong)AccessSize(w);

    /// <summary>无符号偏移访存是否为写：opc=00（整数与 SIMD），或 SIMD 128 位 opc=10。</summary>
    public static bool IsStore(uint w)
    {
        var opc = (w >> 22) & 3;
        var vector = ((w >> 26) & 1) != 0;
        return opc == 0 || (vector && (w >> 30) == 0 && opc == 2);
    }

    /// <summary>
    /// 该指令是否可能改写 Rd 字段（位 0–4）所指的通用寄存器。
    /// 用于 ADRP 配对的失效判断：存储类、比较分支、条件分支和系统指令的位 0–4 不是目的寄存器。
    /// 结论偏保守（宁可失效），只影响配对数量，不会制造错误配对。
    /// </summary>
    public static bool MayWriteRd(uint w)
    {
        if (IsCbz(w) || IsTbz(w) || IsBCond(w) || IsB(w) || IsBl(w) || IsBr(w) || IsBlr(w) || IsRet(w)) return false;
        if ((w & 0xFFC00000) == 0xD5000000 && (w & 0x00200000) == 0) return false;     // 系统指令（MSR、HINT、屏障等）
        if (IsUnsignedOffsetAccess(w)) return !IsStore(w);
        if ((w & 0x3A000000) == 0x28000000) return ((w >> 22) & 1) != 0;              // LDP/STP：L 位
        if ((w & 0x3B200C00) == 0x38000400 || (w & 0x3B200C00) == 0x38000C00 || (w & 0x3B200C00) == 0x38200800)
            return ((w >> 22) & 3) != 0;                                                // 前后变址、寄存器偏移访存
        return true;
    }
}
