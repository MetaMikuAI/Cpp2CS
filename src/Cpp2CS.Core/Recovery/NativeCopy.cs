using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>完整指令副本匹配；分支保留内外目标，其余指令逐字一致，不消除返回值计算。</summary>
internal static class NativeCopy
{
    internal static bool Equal(CodeFunction left, CodeFunction right, Func<ulong, uint?> word)
    {
        if (left.Size != right.Size || left.Size == 0 || left.ExceptionRegions.Length != 0 || right.ExceptionRegions.Length != 0) return false;
        bool Target(ulong a, ulong b) => left.Contains(a) && right.Contains(b)
            ? a - left.Start == b - right.Start : !left.Contains(a) && !right.Contains(b) && a == b;
        for (var offset = 0UL; offset < left.Size; offset += 4)
        {
            var a = left.Start + offset;
            var b = right.Start + offset;
            if (word(a) is not { } x || word(b) is not { } y) return false;
            if (A64.IsB(x) || A64.IsBl(x))
            {
                if ((x & 0xfc000000) != (y & 0xfc000000) || !Target(A64.Imm26Target(x, a), A64.Imm26Target(y, b))) return false;
            }
            else if (A64.IsBCond(x) || A64.IsCbz(x))
            {
                if ((x & ~0x00ffffe0u) != (y & ~0x00ffffe0u) || !Target(A64.Imm19Target(x, a), A64.Imm19Target(y, b))) return false;
            }
            else if (A64.IsTbz(x))
            {
                if ((x & ~0x0007ffe0u) != (y & ~0x0007ffe0u) || !Target(A64.Imm14Target(x, a), A64.Imm14Target(y, b))) return false;
            }
            else if (A64.IsAdr(x) || A64.IsAdrp(x) || (x & 0x3b000000) == 0x18000000 || x != y) return false;
        }
        return true;
    }
}
