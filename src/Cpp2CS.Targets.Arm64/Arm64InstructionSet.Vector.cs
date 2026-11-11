using System.Numerics;
using Cpp2CS.Native.Terms;
using static Cpp2CS.Native.Terms.CoreOperation;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Targets.Arm64;

public sealed partial class Arm64InstructionSet
{
    private sealed partial class Semantics
    {
        private Term Repeat(Term element, int width) => T.Concat(Enumerable.Repeat(element, width / element.Width).ToArray());
        private void InsertV(int index, Term element, int low)
        {
            var old = e.Read(V[index]); var parts = new List<Term>();
            if (low > 0) parts.Add(T.Slice(old, 0, low));
            parts.Add(element);
            if (low + element.Width < 128) parts.Add(T.Slice(old, low + element.Width, 128 - low - element.Width));
            WriteV(index, T.Concat(parts.ToArray()));
        }
        private bool VectorMove()
        {
            int width = Bit(30) ? 128 : 64;
            // ORR 的 MOV 别名与普通 ORR 共用逐位定义。
            if (Is(0xbfe0fc00, 0x0ea01c00)) { WriteV(D, Op(Or, ReadV(A, width), ReadV(M, width))); return true; }
            if (Is(0x9fe08400, 0x0e000400))
            {
                int imm = B(16, 5), op = B(11, 4);
                if (imm == 0) { Hole("vector"); return true; }
                int size = BitOperations.TrailingZeroCount((uint)imm), bits = 8 << size, lane = imm >> (size + 1);
                if (size > 3) { Hole("vector"); return true; }
                if (Bit(29))
                {
                    if (!Bit(30) || (B(11, 4) & ((1 << size) - 1)) != 0) Hole("vector");
                    else InsertV(D, T.Slice(e.Read(V[A]), (B(11, 4) >> size) * bits, bits), lane * bits);
                }
                else if (op == 0 && (bits != 64 || Bit(30))) WriteV(D, Repeat(T.Slice(e.Read(V[A]), lane * bits, bits), width));
                else if (op == 1 && lane == 0 && (bits != 64 || Bit(30))) WriteV(D, Repeat(ReadX(A, bits), width));
                else if (op == 3 && Bit(30)) InsertV(D, ReadX(A, bits), lane * bits);
                else if (op == 5 && bits < (Bit(30) ? 64 : 32)) WriteX(D, Extend(T.Slice(e.Read(V[A]), lane * bits, bits), Bit(30) ? 64 : 32, true));
                else if (op == 7 && (Bit(30) ? bits == 64 : bits < 64)) WriteX(D, Extend(T.Slice(e.Read(V[A]), lane * bits, bits), Bit(30) ? 64 : 32));
                else Hole("vector");
                return true;
            }
            // 标量 DUP 只写所选元素，余下位清零。
            if (Is(0xffe0fc00, 0x5e000400))
            {
                int imm = B(16, 5), size = BitOperations.TrailingZeroCount((uint)imm);
                if (size > 3) Hole("vector");
                else WriteV(D, T.Slice(e.Read(V[A]), (imm >> (size + 1)) * (8 << size), 8 << size));
                return true;
            }
            if (Is(0x9ff80c00, 0x0f000400))
            {
                int mode = B(12, 4), imm = (B(16, 3) << 5) | B(5, 5); bool invert = Bit(29);
                Term value;
                if (mode < 12)
                {
                    int bits = mode < 8 ? 32 : 16, shift = mode < 8 ? (mode >> 1) * 8 : ((mode >> 1) & 1) * 8;
                    value = Repeat(K((BigInteger)imm << shift, bits), width);
                    if ((mode & 1) != 0)
                    { WriteV(D, Op(invert ? And : Or, ReadV(D, width), invert ? Unary(Not, value) : value)); return true; }
                    if (invert) value = Unary(Not, value);
                }
                else if (mode < 14)
                {
                    int shift = mode == 12 ? 8 : 16;
                    value = Repeat(K(((BigInteger)imm << shift) | ((1 << shift) - 1), 32), width);
                    if (invert) value = Unary(Not, value);
                }
                else if (mode == 14)
                {
                    if (!invert) value = Repeat(K(imm, 8), width);
                    else
                    {
                        BigInteger expanded = 0;
                        for (int i = 0; i < 8; i++) if ((imm & (1 << i)) != 0) expanded |= (BigInteger)255 << (i * 8);
                        value = Repeat(K(expanded, 64), width);
                    }
                }
                else
                {
                    if (invert && !Bit(30)) { Hole("vector"); return true; }
                    value = Repeat(K(FloatImmediate(imm, invert ? 64 : 32), invert ? 64 : 32), width);
                }
                WriteV(D, value); return true;
            }
            // FCVTL/FCVTN 的单精度与双精度形式；半精度仍报洞。
            if (Is(0xbf3ffc00, 0x0e217800) || Is(0xbf3ffc00, 0x0e216800))
            {
                if (B(22, 2) != 1) { Hole("vector"); return true; }
                bool widen = Bit(12); var source = e.Read(V[A]);
                var value = T.Concat(Enumerable.Range(0, 2).Select(i => Convert(FloatConvert,
                    T.Slice(source, widen ? (Bit(30) ? 64 : 0) + i * 32 : i * 64, widen ? 32 : 64), widen ? 64 : 32)).ToArray());
                if (!widen && Bit(30)) InsertV(D, value, 64); else WriteV(D, value);
                return true;
            }
            // XTN/XTN2：每个源元素保留低半；第二形式保留目的低 64 位。
            if (Is(0xbf3ffc00, 0x0e212800))
            {
                int bits = 8 << B(22, 2);
                if (bits == 64) Hole("vector");
                else
                {
                    var source = e.Read(V[A]);
                    var value = T.Concat(Enumerable.Range(0, 64 / bits).Select(i => T.Slice(source, i * bits * 2, bits)).ToArray());
                    if (Bit(30)) InsertV(D, value, 64); else WriteV(D, value);
                }
                return true;
            }
            // SSHLL/USHLL（含 SXTL/UXTL 别名），高半形式选源的高 64 位。
            if (Is(0x9f80fc00, 0x0f00a400))
            {
                int imm = B(16, 7), size = BitOperations.Log2((uint)imm), bits = 1 << size;
                if (imm < 8 || bits > 32) Hole("vector");
                else
                {
                    var source = e.Read(V[A]); int shift = imm - bits;
                    WriteV(D, T.Concat(Enumerable.Range(0, 64 / bits).Select(i => Shift(Extend(T.Slice(source, (Bit(30) ? 64 : 0) + i * bits, bits), bits * 2, !Bit(29)), 0, shift)).ToArray()));
                }
                return true;
            }
            // FMOV 在 X 与 V 的高 64 位间搬运，写高半时保留低半。
            if (Is(0xfffffc00, 0x9eae0000)) { WriteX(D, T.Slice(e.Read(V[A]), 64, 64)); return true; }
            if (Is(0xfffffc00, 0x9eaf0000)) { InsertV(D, ReadX(A, 64), 64); return true; }
            return false;
        }
    }
}
