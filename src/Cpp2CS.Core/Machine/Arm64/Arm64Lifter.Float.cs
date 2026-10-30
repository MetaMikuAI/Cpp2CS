using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Arm64;



public static partial class Arm64Lifter
{
    private sealed partial class Context
    {
        private int FloatWidth => Bits(22, 2) switch { 0 => 32, 1 => 64, 3 => 16, _ => 0 };

        private void FloatSimd()
        {
            if ((w & 0x5F000000) == 0x1E000000 && !Bit(29)) { FloatScalar(); return; }
            if ((w & 0xDF000000) == 0x1F000000 && !Bit(29)) { FloatMultiplyAdd(); return; }
            if ((w & 0x9FF80400) == 0x0F000400) { ModifiedImmediate(); return; }
            if ((w & 0x9FE08400) == 0x0E000400) { SimdCopy(); return; }
            if ((w & 0xFFE0FC00) == 0x5E000400) { ScalarDuplicate(); return; }
            if (VectorDispatch()) return;
            Unsupported("simd");
        }

        private void FloatScalar()
        {
            var width = FloatWidth;
            if ((w & 0x5F20FC00) == 0x1E200000) { FloatInteger(); return; }
            if (width == 0) { Unsupported("fp.type"); return; }
            if ((w & 0x5F207C00) == 0x1E204000 && !Bit(31)) { FloatUnary(width); return; }
            if ((w & 0x5F203C00) == 0x1E202000 && !Bit(31))
            {
                var opcode2 = Bits(0, 5);
                if ((opcode2 & 0b00111) != 0) { Unsupported("fcmp.opcode2"); return; }
                var left = V(Rn, width);
                var right = (opcode2 & 0b01000) != 0 ? C(0, width) : V(Rm, width);
                SetFlags(new Flags(FlagKind.FloatCompare, left, right, width));
                return;
            }
            if ((w & 0x5F201FE0) == 0x1E201000 && !Bit(31))
            {
                SetV(Rd, C(ExpandFloatImmediate(Bits(13, 8), width), width));
                return;
            }
            if ((w & 0x5F200C00) == 0x1E200400 && !Bit(31))
            {
                var taken = new Flags(FlagKind.FloatCompare, V(Rn, width), V(Rm, width), width);
                SetFlags(new ConditionalFlags(Condition(Bits(12, 4)), taken, (byte)Bits(0, 4)));
                return;
            }
            if ((w & 0x5F200C00) == 0x1E200800 && !Bit(31))
            {
                var left = V(Rn, width);
                var right = V(Rm, width);
                Expr? result = Bits(12, 4) switch
                {
                    0 => Op(BinOp.FMul, left, right),
                    1 => Op(BinOp.FDiv, left, right),
                    2 => Op(BinOp.FAdd, left, right),
                    3 => Op(BinOp.FSub, left, right),
                    4 => Op(BinOp.FMax, left, right),
                    5 => Op(BinOp.FMin, left, right),
                    6 => Op(BinOp.FMaxNumber, left, right),
                    7 => Op(BinOp.FMinNumber, left, right),
                    8 => new Unary(UnOp.FNeg, Op(BinOp.FMul, left, right), width),
                    _ => null,
                };
                if (result is null) { Unsupported("fp.2source"); return; }
                SetV(Rd, result);
                return;
            }
            if ((w & 0x5F200C00) == 0x1E200C00 && !Bit(31))
            {
                SetV(Rd, new Select(Condition(Bits(12, 4)), V(Rn, width), V(Rm, width), width));
                return;
            }
            Unsupported("fp.scalar");
        }

        private void FloatUnary(int width)
        {
            var opcode = Bits(15, 6);
            var operand = V(Rn, width);
            if (opcode is >= 4 and <= 7)
            {
                var target = (opcode & 3) switch { 0 => 32, 1 => 64, 3 => 16, _ => 0 };
                if (target == 0 || target == width) { Unsupported("fcvt.type"); return; }
                SetV(Rd, new Ir.Convert(ConvKind.FloatToFloat, operand, target));
                return;
            }
            UnOp? op = opcode switch
            {
                1 => UnOp.FAbs,
                2 => UnOp.FNeg,
                3 => UnOp.FSqrt,
                8 => UnOp.FRoundEven,
                9 => UnOp.FCeil,
                10 => UnOp.FFloor,
                11 => UnOp.FTrunc,
                12 => UnOp.FRoundAway,
                14 or 15 => UnOp.FRoundCurrent,
                _ => null,
            };
            if (opcode == 0) { SetV(Rd, operand); return; }
            if (op is null) { Unsupported("fp.1source"); return; }
            SetV(Rd, new Unary(op.Value, operand, width));
        }

        private void FloatMultiplyAdd()
        {
            var width = FloatWidth;
            if (width == 0) { Unsupported("fp.3source.type"); return; }
            var product = Op(BinOp.FMul, V(Rn, width), V(Rm, width));
            var addend = V(Ra, width);
            Expr result = ((Bit(21) ? 2 : 0) | (Bit(15) ? 1 : 0)) switch
            {
                0 => Op(BinOp.FAdd, addend, product),
                1 => Op(BinOp.FSub, addend, product),
                2 => Op(BinOp.FSub, new Unary(UnOp.FNeg, addend, width), product),
                _ => Op(BinOp.FSub, product, addend),
            };
            SetV(Rd, result);
        }

        private void FloatInteger()
        {
            var intWidth = Sf;
            var rmode = Bits(19, 2);
            var opcode = Bits(16, 3);
            var type = Bits(22, 2);
            if (opcode is 6 or 7)
            {
                // fmov 在通用寄存器与浮点寄存器之间搬运位模式
                if (rmode == 1 && type == 2 && intWidth == 64)
                {
                    if (opcode == 6) SetX(Rd, new Extract(V(Rn, 128), 64, 64));
                    else SetV(Rd, new Insert(V(Rd, 128), X(Rn, 64), 64));
                    return;
                }
                var width = FloatWidth;
                if (rmode != 0 || width == 0 || (width != intWidth && width != 16)) { Unsupported("fmov.general"); return; }
                if (opcode == 6) SetX(Rd, new Ir.Convert(ConvKind.Bitcast, V(Rn, width), width));
                else SetV(Rd, new Ir.Convert(ConvKind.Bitcast, X(Rn, width), width));
                return;
            }
            var floatWidth = FloatWidth;
            if (floatWidth == 0) { Unsupported("fcvt.type"); return; }
            if (opcode is 2 or 3)
            {
                if (rmode != 0) { Unsupported("cvtf.rmode"); return; }
                SetV(Rd, new Ir.Convert(opcode == 2 ? ConvKind.SIntToFloat : ConvKind.UIntToFloat, X(Rn, intWidth), floatWidth));
                return;
            }
            UnOp? rounding = (rmode, opcode) switch
            {
                (0, 0 or 1) => UnOp.FRoundEven,
                (0, 4 or 5) => UnOp.FRoundAway,
                (1, 0 or 1) => UnOp.FCeil,
                (2, 0 or 1) => UnOp.FFloor,
                (3, 0 or 1) => null,
                _ => UnOp.Neg,
            };
            if (rounding == UnOp.Neg) { Unsupported("fcvt.int"); return; }
            Expr source = V(Rn, floatWidth);
            if (rounding is not null) source = new Unary(rounding.Value, source, floatWidth);
            var unsigned = (opcode & 1) != 0;
            SetX(Rd, new Ir.Convert(unsigned ? ConvKind.FloatToUInt : ConvKind.FloatToSInt, source, intWidth));
        }

        private static ulong ExpandFloatImmediate(uint imm8, int width)
        {
            var (exponentBits, fractionBits) = width switch { 16 => (5, 10), 32 => (8, 23), _ => (11, 52) };
            var sign = (ulong)(imm8 >> 7) & 1;
            var b6 = (imm8 >> 6) & 1;
            var exponent = ((ulong)(b6 ^ 1) << (exponentBits - 1))
                | ((b6 == 1 ? (1UL << (exponentBits - 3)) - 1 : 0) << 2)
                | ((imm8 >> 4) & 3);
            var fraction = (ulong)(imm8 & 0xF) << (fractionBits - 4);
            return (sign << (width - 1)) | (exponent << fractionBits) | fraction;
        }

        private void ModifiedImmediate()
        {
            var q = Bit(30);
            var op = Bit(29);
            var cmode = Bits(12, 4);
            var imm8 = (Bits(16, 3) << 5) | Bits(5, 5);
            var width = q ? 128 : 64;
            ulong value;
            if (cmode == 0xF)
            {
                if (!op) value = Replicate(ExpandFloatImmediate(imm8, 32), 32);
                else if (q) value = ExpandFloatImmediate(imm8, 64);
                else { Unsupported("fmov.vector"); return; }
            }
            else if (cmode == 0xE && op)
            {
                value = 0;
                for (var i = 0; i < 8; i++)
                    if (((imm8 >> i) & 1) != 0) value |= 0xFFUL << (i * 8);
            }
            else if ((cmode & 1) == 1 && cmode < 0xC)
            {
                var size = cmode < 8 ? 32 : 16;
                var shift = 8 * (int)((cmode >> 1) & (cmode < 8 ? 3u : 1u));
                var immediate = (ulong)imm8 << shift;
                SetLanes(width, size, i => Op(op ? BinOp.And : BinOp.Or, Lane(Rd, i, size),
                    C(op ? ~immediate & Expr.Mask(size) : immediate, size)));
                return;
            }
            else
            {
                value = cmode switch
                {
                    < 8 => Replicate((ulong)imm8 << (int)(8 * (cmode >> 1)), 32),
                    < 0xC => Replicate((ulong)imm8 << (int)(8 * ((cmode >> 1) & 1)), 16),
                    0xC => Replicate(((ulong)imm8 << 8) | 0xFF, 32),
                    0xD => Replicate(((ulong)imm8 << 16) | 0xFFFF, 32),
                    _ => Replicate(imm8, 8),
                };
                if (op) value = ~value;
            }
            SetV(Rd, value == 0 ? C(0, width) : q ? new Intrinsic("vdup.64", [C(value, 64)], 128) : C(value, 64));
        }

        private static ulong Replicate(ulong value, int size)
        {
            var result = 0UL;
            for (var i = 0; i < 64; i += size) result |= (value & Expr.Mask(size)) << i;
            return result;
        }

        private (int Size, int Index) Element(uint imm5)
        {
            var size = System.Numerics.BitOperations.TrailingZeroCount(imm5);
            if (size > 3) return (0, -1);
            return (8 << size, (int)(imm5 >> (size + 1)));
        }

        private void SimdCopy()
        {
            var q = Bit(30);
            var op = Bit(29);
            var imm4 = Bits(11, 4);
            var (size, index) = Element(Bits(16, 5));
            if (index < 0) { Unsupported("simd.copy.imm5"); return; }
            var width = q ? 128 : 64;
            if (op)
            {
                if (!q) { Unsupported("simd.copy.op"); return; }
                var source = (int)(imm4 >> (System.Numerics.BitOperations.Log2((uint)size) - 3));
                SetV(Rd, new Insert(V(Rd, 128), Field(V(Rn, 128), source * size, size), index * size));
                return;
            }
            switch (imm4)
            {
                case 0:
                    SetV(Rd, new Intrinsic($"vdup.{size}", [Field(V(Rn, 128), index * size, size)], width));
                    return;
                case 1:
                    SetV(Rd, new Intrinsic($"vdup.{size}", [X(Rn, size)], width));
                    return;
                case 3 when q:
                    SetV(Rd, new Insert(V(Rd, 128), X(Rn, size), index * size));
                    return;
                case 5:
                    SetX(Rd, SExt(Field(V(Rn, 128), index * size, size), q ? 64 : 32));
                    return;
                case 7:
                    SetX(Rd, Field(V(Rn, 128), index * size, size));
                    return;
                default:
                    Unsupported("simd.copy");
                    return;
            }
        }

        private void ScalarDuplicate()
        {
            var (size, index) = Element(Bits(16, 5));
            if (index < 0) { Unsupported("dup.scalar"); return; }
            SetV(Rd, Field(V(Rn, 128), index * size, size));
        }
    }
}
