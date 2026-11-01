using Cpp2CS.Ir;

namespace Cpp2CS.Facts;

/// <summary>异常事实所需的寄存器来源解码；未知编码使整个路径无法证明。</summary>
internal static class A64ValueFlow
{
    public static IReadOnlyList<Stmt> Decode(ulong pc, uint word)
    {
        var result = new List<Stmt>();
        var rd = A64.Rd(word);
        var rn = A64.Rn(word);
        var width = (word >> 31) != 0 ? 64 : 32;
        Expr Read(int register, int bits = 64) => register == 31 ? Expr.C(0, bits) : new Read(Storage.Gpr(register), bits);
        void Write(int register, Expr value) { if (register != 31) result.Add(new Assign(pc, Storage.Gpr(register), value)); }
        void Unknown(int register) => Write(register, new Ir.Unknown("非地址来源", 64));
        if (A64.IsAdr(word) || A64.IsAdrp(word)) Write(rd, Expr.C(A64.IsAdr(word) ? A64.AdrTarget(word, pc) : A64.AdrpPage(word, pc), 64));
        else if ((word & 0x1f800000) == 0x11000000)
        {
            var source = new Read(Storage.Gpr(rn), width);
            Write(rd, new Binary((word & 0x40000000) == 0 ? BinOp.Add : BinOp.Sub, source, Expr.C(A64.AddImmediate(word), width), width));
        }
        else if ((word & 0x7fe0ffe0) == 0x2a0003e0) Write(rd, Read((int)((word >> 16) & 31), width));
        else if ((word & 0x1f800000) == 0x12800000 && (width == 64 || ((word >> 21) & 3) < 2) && ((word >> 29) & 3) is 0 or 2 or 3)
        {
            var shift = (int)((word >> 21) & 3) * 16;
            var immediate = (ulong)((word >> 5) & 0xffff);
            Write(rd, ((word >> 29) & 3) switch
            {
                0 => Expr.C(~(immediate << shift), width),
                2 => Expr.C(immediate << shift, width),
                _ => new Insert(Read(rd, width), Expr.C(immediate, 16), shift),
            });
        }
        else if ((word & 0x3fe00800) == 0x1a800000) Unknown(rd); // CSEL/CSINC/CSINV/CSNEG
        else if ((word & 0x1f200000) == 0x0b000000 && rd == 31 && ((word >> 22) & 3) < 3
            && (width == 64 || ((word >> 10) & 63) < 32)) { } // 只写标志或丢弃结果的 ADD/SUB
        else if (A64.IsBl(word) || A64.IsBlr(word))
            result.Add(new Call(pc, CallKind.Direct, Expr.C(0, 64)));
        else if (A64.IsB(word) || A64.ConditionalTarget(word, pc) is not null || A64.IsRet(word) || A64.IsTrap(word) || word == A64.Nop) { }
        else if (A64.IsUnsignedOffsetAccess(word))
        {
            if ((word & 0x04000000) == 0 && !A64.IsStore(word)) Unknown(rd);
        }
        else if ((word & 0x3a000000) == 0x28000000)
        {
            var load = (word & 0x00400000) != 0;
            var vector = (word & 0x04000000) != 0;
            if (load && !vector) { Unknown(rd); Unknown((int)((word >> 10) & 31)); }
            if (((word >> 23) & 3) is 1 or 3) Unknown(rn);
        }
        else if ((word & 0x3b200000) == 0x38000000)
        {
            if ((word & 0x04000000) == 0 && ((word >> 22) & 3) != 0) Unknown(rd);
            if (((word >> 10) & 3) is 1 or 3) Unknown(rn);
        }
        else result.Add(new Opaque(pc, $"异常来源未解码 0x{word:x8}"));
        return result;
    }
}
