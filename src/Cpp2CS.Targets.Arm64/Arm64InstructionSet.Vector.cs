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
                if (imm == 0) { VectorHole("向量复制", $"Q={B(30)} op={B(29)} imm5=0x{B(16, 5):x} imm4=0x{B(11, 4):x}"); return true; }
                int size = BitOperations.TrailingZeroCount((uint)imm), bits = 8 << size, lane = imm >> (size + 1);
                if (size > 3) { VectorHole("向量复制", $"Q={B(30)} op={B(29)} imm5=0x{B(16, 5):x} imm4=0x{B(11, 4):x}"); return true; }
                if (Bit(29))
                {
                    if (!Bit(30) || (B(11, 4) & ((1 << size) - 1)) != 0) VectorHole("向量复制", $"Q={B(30)} op={B(29)} imm5=0x{B(16, 5):x} imm4=0x{B(11, 4):x}");
                    else InsertV(D, T.Slice(e.Read(V[A]), (B(11, 4) >> size) * bits, bits), lane * bits);
                }
                else if (op == 0 && (bits != 64 || Bit(30))) WriteV(D, Repeat(T.Slice(e.Read(V[A]), lane * bits, bits), width));
                else if (op == 1 && lane == 0 && (bits != 64 || Bit(30))) WriteV(D, Repeat(ReadX(A, bits), width));
                else if (op == 3 && Bit(30)) InsertV(D, ReadX(A, bits), lane * bits);
                else if (op == 5 && bits < (Bit(30) ? 64 : 32)) WriteX(D, Extend(T.Slice(e.Read(V[A]), lane * bits, bits), Bit(30) ? 64 : 32, true));
                else if (op == 7 && (Bit(30) ? bits == 64 : bits < 64)) WriteX(D, Extend(T.Slice(e.Read(V[A]), lane * bits, bits), Bit(30) ? 64 : 32));
                else VectorHole("向量复制", $"Q={B(30)} op={B(29)} imm5=0x{B(16, 5):x} imm4=0x{B(11, 4):x}");
                return true;
            }
            // 标量 DUP 只写所选元素，余下位清零。
            if (Is(0xffe0fc00, 0x5e000400))
            {
                int imm = B(16, 5), size = BitOperations.TrailingZeroCount((uint)imm);
                if (size > 3) VectorHole("标量复制", $"imm5=0x{B(16, 5):x}");
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
                    if (invert && !Bit(30)) { VectorHole("向量修改立即数", $"Q={B(30)} op={B(29)} cmode=0x{B(12, 4):x}"); return true; }
                    value = Repeat(K(FloatImmediate(imm, invert ? 64 : 32), invert ? 64 : 32), width);
                }
                WriteV(D, value); return true;
            }
            // SSHLL/USHLL（含 SXTL/UXTL 别名），高半形式选源的高 64 位。
            if (Is(0x9f80fc00, 0x0f00a400))
            {
                int imm = B(16, 7), size = BitOperations.Log2((uint)imm), bits = 1 << size;
                if (imm < 8 || bits > 32) VectorHole("向量立即数移位", $"U={B(29)} immh=0x{B(19, 4):x} immb=0x{B(16, 3):x} opcode=0x{B(11, 5):x}");
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
        private void VectorHole(string encoding, string? fields = null) => Hole("vector",
            $"{encoding}：{fields ?? $"Q={B(30)} U={B(29)} size={B(22, 2)} opcode=0x{B(12, 5):x}"}");
        private void VectorLanes(int bits, int width, Func<int, Term> element) =>
            WriteV(D, T.Concat(Enumerable.Range(0, width / bits).Select(element).ToArray()));
        private bool Vector()
        {
            bool scalar = Bit(28);
            if (Is(0xbf000000, 0x0d000000)) { VectorStructure(); return true; }
            if (scalar && !Bit(30)) return false;
            if (Is(0x8f3e0c00, 0x0e200800)) { VectorMisc(scalar); return true; }
            if (Is(0x8f200400, 0x0e200400)) { VectorSame(scalar); return true; }
            if (Is(0x8f000400, 0x0f000000)) { VectorElement(scalar); return true; }
            if (Is(0xbf208400, 0x2e000000))
            {
                int width = Bit(30) ? 128 : 64, offset = B(11, 4) * 8;
                if (B(22, 2) != 0 || offset >= width)
                    VectorHole("向量提取", $"Q={B(30)} op2={B(22, 2)} imm4=0x{B(11, 4):x}");
                else WriteV(D, T.Slice(T.Concat(ReadV(A, width), ReadV(M, width)), offset, width));
                return true;
            }
            if (Is(0x9f3e0c00, 0x0e300800))
            {
                int size = B(22, 2), bits = 8 << size, width = Bit(30) ? 128 : 64;
                if (Bit(29) || B(12, 5) != 0x1b || size == 3 || (size == 2 && !Bit(30))) VectorHole("向量跨元素归约");
                else
                {
                    var source = ReadV(A, width); var sum = T.Slice(source, 0, bits);
                    for (int i = 1; i < width / bits; i++) sum = Op(Add, sum, T.Slice(source, i * bits, bits));
                    WriteV(D, sum);
                }
                return true;
            }
            return false;
        }
        private void VectorMisc(bool scalar)
        {
            int size = B(22, 2), opcode = B(12, 5), width = scalar ? 32 << (size & 1) : Bit(30) ? 128 : 64;
            var source = e.Read(V[A]);
            // FCVTL/FCVTN 和 XTN 与其余二寄存器杂项共用类入口。
            if (!scalar && !Bit(29) && opcode is 0x16 or 0x17)
            {
                if (size != 1) { VectorHole("向量二寄存器杂项"); return; }
                bool widen = opcode == 0x17;
                var value = T.Concat(Enumerable.Range(0, 2).Select(i => Convert(FloatConvert,
                    T.Slice(source, widen ? (Bit(30) ? 64 : 0) + i * 32 : i * 64, widen ? 32 : 64), widen ? 64 : 32)).ToArray());
                if (!widen && Bit(30)) InsertV(D, value, 64); else WriteV(D, value);
            }
            else if (!scalar && !Bit(29) && opcode == 0x12)
            {
                if (size == 3) { VectorHole("向量二寄存器杂项"); return; }
                int bits = 8 << size;
                var value = T.Concat(Enumerable.Range(0, 64 / bits).Select(i => T.Slice(source, i * bits * 2, bits)).ToArray());
                if (Bit(30)) InsertV(D, value, 64); else WriteV(D, value);
            }
            else if (opcode == 0x1d && size < 2 && (scalar || size == 0 || Bit(30)))
            {
                int bits = 32 << size;
                VectorLanes(bits, width, i => Convert(Bit(29) ? UnsignedToFloat : SignedToFloat, T.Slice(source, i * bits, bits), bits));
            }
            else if (!scalar && !Bit(29) && opcode == 0xf && size >= 2 && (size == 2 || Bit(30)))
            {
                int bits = 32 << (size & 1);
                VectorLanes(bits, width, i => Unary(FloatAbs, T.Slice(source, i * bits, bits)));
            }
            else if (!scalar && !Bit(29) && opcode == 0 && size < 3)
            {
                int bits = 8 << size, perBlock = 64 / bits;
                VectorLanes(bits, width, i => T.Slice(source, (i / perBlock * perBlock + perBlock - 1 - i % perBlock) * bits, bits));
            }
            else VectorHole(scalar ? "标量二寄存器杂项" : "向量二寄存器杂项");
        }
        private void VectorSame(bool scalar)
        {
            int size = B(22, 2), opcode = B(11, 5), u = B(29);
            string encoding = scalar ? "标量三操作数同型" : "向量三操作数同型";
            string fields = $"Q={B(30)} U={u} size={size} opcode=0x{opcode:x}";
            CoreOperation? floating = (u, opcode, size) switch
            {
                (0, 0x1a, _) when !scalar => size < 2 ? FloatAdd : FloatSubtract,
                (1, 0x1a, >= 2) => FloatSubtract,
                (1, 0x1b, < 2) when !scalar => FloatMultiply,
                (1, 0x1f, < 2) when !scalar => FloatDivide,
                _ => null
            };
            int bits = floating is null ? 8 << size : 32 << (size & 1);
            int width = scalar ? bits : Bit(30) ? 128 : 64;
            if (floating is { } operation)
            {
                if (!scalar && bits == 64 && !Bit(30)) { VectorHole(encoding, fields); return; }
                var a = ReadV(A, width); var b = ReadV(M, width);
                VectorLanes(bits, width, i =>
                {
                    var result = Op(operation, T.Slice(a, i * bits, bits), T.Slice(b, i * bits, bits));
                    return u == 1 && opcode == 0x1a ? Unary(FloatAbs, result) : result;
                });
                return;
            }
            bool integer = !scalar && (opcode == 0x10 || (u == 0 && opcode == 0x6)
                ? size != 3 || Bit(30)
                : u == 0 && size < 3 && opcode is 0x13 or 0xc or 0xd);
            if (!integer) { VectorHole(encoding, fields); return; }
            var left = ReadV(A, width); var right = ReadV(M, width);
            VectorLanes(bits, width, i =>
            {
                var a = T.Slice(left, i * bits, bits); var b = T.Slice(right, i * bits, bits);
                return opcode switch
                {
                    0x10 => Op(u == 0 ? Add : Subtract, a, b),
                    0x13 => Op(Multiply, a, b),
                    0xc => Choose(Compare(SignedLess, a, b), b, a),
                    0xd => Choose(Compare(SignedLess, a, b), a, b),
                    _ => Choose(Compare(SignedLess, b, a), K(-1, bits), K(0, bits))
                };
            });
        }
        private void VectorElement(bool scalar)
        {
            int size = B(22, 2), opcode = B(12, 4), bits = 32 << (size & 1);
            if (Bit(29) || opcode != 9 || size < 2 || (size == 3 && (Bit(21) || (!scalar && !Bit(30)))))
            {
                VectorHole(scalar ? "标量按元素运算" : "向量按元素运算",
                    $"Q={B(30)} U={B(29)} size={size} opcode=0x{opcode:x} H={B(11)} L={B(21)} M={B(20)}");
                return;
            }
            // 单精度下标为 H:L，双精度为 H；M 是这两种形式的寄存器号高位。
            int lane = size == 2 ? (B(11) << 1) | B(21) : B(11);
            int width = scalar ? bits : Bit(30) ? 128 : 64;
            var a = ReadV(A, width); var element = T.Slice(e.Read(V[M]), lane * bits, bits);
            VectorLanes(bits, width, i => Op(FloatMultiply, T.Slice(a, i * bits, bits), element));
        }
        private void VectorStructure()
        {
            int opcode = B(13, 3), size = B(10, 2), scale = opcode >> 1, lane = 0;
            bool replicate = scale == 3, load = Bit(22), post = Bit(23);
            bool valid = !Bit(21) && (opcode & 1) == 0 && (post || M == 0);
            if (replicate) { valid &= load && !Bit(12); scale = size; }
            else if (scale == 0) lane = (B(30) << 3) | (B(12) << 2) | size;
            else if (scale == 1) { valid &= (size & 1) == 0; lane = (B(30) << 2) | (B(12) << 1) | (size >> 1); }
            else
            {
                valid &= size < 2;
                if (size == 0) lane = (B(30) << 1) | B(12);
                else { valid &= !Bit(12); lane = B(30); scale = 3; }
            }
            if (!valid)
            {
                VectorHole("向量单结构访存", $"Q={B(30)} L={B(22)} R={B(21)} opcode=0x{opcode:x} S={B(12)} size={size} post={B(23)} Rm={M}");
                return;
            }
            int bits = 8 << scale;
            var address = ReadX(A, 64, true);
            // 后变址寄存器可与基址相同，更新值必须取自访存前。
            var increment = post ? M == 31 ? K(bits / 8) : ReadX(M, 64) : null;
            if (!load) e.Store(address, T.Slice(e.Read(V[D]), lane * bits, bits));
            else if (replicate) WriteV(D, Repeat(e.Load(address, bits), Bit(30) ? 128 : 64));
            else InsertV(D, e.Load(address, bits), lane * bits);
            if (increment is not null) WriteX(A, Op(Add, address, increment), true);
        }
    }
}
