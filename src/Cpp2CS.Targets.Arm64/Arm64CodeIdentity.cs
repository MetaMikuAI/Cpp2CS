using System.Collections.Immutable;
using Cpp2CS.Native.Images;

namespace Cpp2CS.Targets.Arm64;

/// <summary>函数代码与位置无关的写法：指向函数外的相对寻址换成绝对目标，其余指令字原样。
/// 两个函数的写法相同，就是同一段代码放在两个位置：指令、访问的数据地址、调用与跳转的目标都相同。</summary>
public static class Arm64CodeIdentity
{
    private const ulong Relocated = 1UL << 32;

    public static ImmutableArray<ulong>? Create(IImage image, FunctionRange range)
    {
        if (!range.HasConsistentExtent || range.Length == 0 || range.Length % 4 != 0 || !image.IsExecutable(range.Start, range.Length)) return null;
        var code = ImmutableArray.CreateBuilder<ulong>(checked((int)(range.Length / 4)));
        for (ulong offset = 0; offset < range.Length; offset += 4)
        {
            ulong address = range.Start + offset;
            uint word = (uint)image.ReadUnsigned(address, 4);
            uint mask; long displacement; bool page = false;
            if ((word & 0x7c000000) == 0x14000000) { mask = 0x03ffffff; displacement = Signed(word & mask, 26) * 4; }            // B、BL
            else if ((word & 0xff000010) == 0x54000000 || (word & 0x7e000000) == 0x34000000 || (word & 0x3b000000) == 0x18000000)
            { mask = 0x00ffffe0; displacement = Signed((word >> 5) & 0x7ffff, 19) * 4; }                                         // B.cond、CBZ、CBNZ、取字面量
            else if ((word & 0x7e000000) == 0x36000000) { mask = 0x0007ffe0; displacement = Signed((word >> 5) & 0x3fff, 14) * 4; } // TBZ、TBNZ
            else if ((word & 0x1f000000) == 0x10000000)
            {
                mask = 0x60ffffe0; page = (word & 0x80000000) != 0;                                                              // ADR、ADRP
                displacement = Signed(((word >> 5) & 0x7ffff) << 2 | (word >> 29) & 3, 21);
                if (page) displacement <<= 12;
            }
            else { code.Add(word); continue; }
            ulong target = unchecked((page ? address & ~0xfffUL : address) + (ulong)displacement);
            // 函数内的目标随函数一起移动，位移相同就是同一处；页地址总按绝对值比较。
            if (!page && target >= range.Start && target - range.Start < range.Length) { code.Add(word); continue; }
            code.Add(Relocated | word & ~mask);
            code.Add(target);
        }
        return code.ToImmutable();
    }

    public static ulong Hash(ImmutableArray<ulong> code)
    {
        ulong hash = 14695981039346656037;
        foreach (ulong item in code) hash = unchecked((hash ^ item) * 1099511628211);
        return hash;
    }

    private static long Signed(uint value, int bits) => (long)((ulong)value << (64 - bits)) >> (64 - bits);
}
