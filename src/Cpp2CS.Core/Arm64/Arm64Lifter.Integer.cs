using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    private sealed partial class Context
    {
        // ---------- 访存 ----------
        private void LoadStore()
        {
            if ((w & 0x3B000000) == 0x39000000)
            {
                var (bytes, ok) = AccessSize();
                if (!ok) return;
                var offset = (ulong)Bits(10, 12) * (ulong)bytes;
                Single(bytes, Address(XSp(Rn, 64), offset), writeback: null);
                return;
            }
            if ((w & 0x3B200000) == 0x38000000)
            {
                var (bytes, ok) = AccessSize();
                if (!ok) return;
                var imm = (long)((int)(Bits(12, 9) << 23) >> 23);
                var mode = Bits(10, 2);
                var basis = XSp(Rn, 64);
                switch (mode)
                {
                    case 0 or 2: Single(bytes, Address(basis, (ulong)imm), writeback: null); break;
                    case 1: Single(bytes, basis, writeback: Address(basis, (ulong)imm)); break;
                    default:
                        // 先写回再访问：后续访问基于写回后的基址
                        SetXSp(Rn, Address(basis, (ulong)imm));
                        Single(bytes, basis, writeback: null);
                        break;
                }
                return;
            }
            if ((w & 0x3B200C00) == 0x38200800)
            {
                var (bytes, ok) = AccessSize();
                if (!ok) return;
                var option = Bits(13, 3);
                var amount = Bit(12) ? System.Numerics.BitOperations.Log2((uint)bytes) : 0;
                Expr index = option switch
                {
                    2 => ZExt(X(Rm, 32), 64),
                    3 => X(Rm, 64),
                    6 => SExt(X(Rm, 32), 64),
                    7 => X(Rm, 64),
                    _ => null!,
                };
                if (index is null) { Unsupported("ldst.register.option"); return; }
                if (amount != 0) index = Op(BinOp.Shl, index, C((ulong)amount, 64));
                Single(bytes, Add(XSp(Rn, 64), index), writeback: null);
                return;
            }
            if ((w & 0x3A000000) == 0x28000000)
            {
                Pair();
                return;
            }
            if ((w & 0x3B000000) == 0x18000000)
            {
                var target = Imm19Target();
                var address = C(target, 64);
                var vector = Bit(26);
                switch (Bits(30, 2))
                {
                    case 0: Access(vector, true, 4, false, Rd, address); break;
                    case 1: Access(vector, true, 8, false, Rd, address); break;
                    case 2 when vector: Access(true, true, 16, false, Rd, address); break;
                    case 2: Access(false, true, 4, true, Rd, address, signedWidth: 64); break;
                    default: Emit(new Nop(pc, "prfm")); break;
                }
                return;
            }
            if ((w & 0x3FFFFC00) == 0x08DFFC00 || (w & 0x3FFFFC00) == 0x38BFC000)
            {
                // LDAR / LDAPR：获取语义的普通加载
                var bytes = 1 << (int)Bits(30, 2);
                Access(false, true, bytes, false, Rd, XSp(Rn, 64));
                return;
            }
            if ((w & 0x3FFFFC00) == 0x089FFC00)
            {
                var bytes = 1 << (int)Bits(30, 2);
                Access(false, false, bytes, false, Rd, XSp(Rn, 64));
                return;
            }
            if (SingleStructure()) return;
            Unsupported("loadstore");
        }

        private static Expr Address(Expr basis, ulong offset) => offset == 0 ? basis : Add(basis, C(offset, 64));

        /// <summary>单寄存器访问的大小。返回 ok=false 时已输出 Opaque 或 Nop。</summary>
        private (int Bytes, bool Ok) AccessSize()
        {
            var size = (int)Bits(30, 2);
            var opc = Bits(22, 2);
            if (Bit(26))
            {
                if (size == 0 && opc >= 2) return (16, true);
                if (opc >= 2) { Unsupported("ldst.vector.opc"); return (0, false); }
                return (1 << size, true);
            }
            if (opc == 2 && size == 3) { Emit(new Nop(pc, "prfm")); return (0, false); }
            if (opc == 3 && size >= 2) { Unsupported("ldst.opc"); return (0, false); }
            return (1 << size, true);
        }

        private void Single(int bytes, Expr address, Expr? writeback)
        {
            var opc = Bits(22, 2);
            var vector = Bit(26);
            if (vector) Access(true, (opc & 1) != 0, bytes, false, Rd, address);
            else if (opc == 0) Access(false, false, bytes, false, Rd, address);
            else if (opc == 1) Access(false, true, bytes, false, Rd, address);
            else Access(false, true, bytes, true, Rd, address, signedWidth: opc == 2 ? 64 : 32);
            if (writeback is not null) SetXSp(Rn, writeback);
        }

        private void Access(bool vector, bool load, int bytes, bool signed, int rt, Expr address, int signedWidth = 64)
        {
            var bits = bytes * 8;
            if (load)
            {
                Expr value = new Load(address, bits);
                if (vector) SetV(rt, value);
                else SetX(rt, signed ? SExt(value, signedWidth) : value);
            }
            else
            {
                var value = vector ? V(rt, bits) : X(rt, bits);
                Emit(new Store(pc, address, value));
            }
        }

        private void Pair()
        {
            var opc = Bits(30, 2);
            var vector = Bit(26);
            var load = Bit(22);
            var mode = Bits(23, 2);
            int bytes;
            var signed = false;
            if (vector) bytes = opc switch { 0 => 4, 1 => 8, 2 => 16, _ => 0 };
            else if (opc == 0) bytes = 4;
            else if (opc == 1 && load) { bytes = 4; signed = true; }
            else if (opc == 2) bytes = 8;
            else bytes = 0;
            if (bytes == 0) { Unsupported("ldst.pair.opc"); return; }
            var imm = (long)((int)(Bits(15, 7) << 25) >> 25) * bytes;
            var rt2 = (int)Bits(10, 5);
            Expr basis = XSp(Rn, 64);
            // 加载目标与基址重叠时先把基址存进临时单元，避免第二次访问看到被覆盖的基址
            if (load && !vector && (Rd == Rn || rt2 == Rn) && Rn != 31)
            {
                Emit(new Assign(pc, Storage.Temp(0), basis));
                basis = new Read(Storage.Temp(0), 64);
            }
            Expr first;
            Expr? writeback = null;
            switch (mode)
            {
                case 1: first = basis; writeback = Address(basis, (ulong)imm); break;
                case 3:
                    SetXSp(Rn, Address(basis, (ulong)imm));
                    first = XSp(Rn, 64);
                    break;
                default: first = Address(basis, (ulong)imm); break;
            }
            var second = Address(first, (ulong)bytes);
            Access(vector, load, bytes, signed, Rd, first);
            Access(vector, load, bytes, signed, rt2, second);
            if (writeback is not null) SetXSp(Rn, writeback);
        }

        // ---------- 数据处理（寄存器） ----------
        private void DataRegister()
        {
            if ((w & 0x1F000000) == 0x0A000000) { LogicalShifted(); return; }
            if ((w & 0x1F200000) == 0x0B000000) { AddSubShifted(); return; }
            if ((w & 0x1F200000) == 0x0B200000) { AddSubExtended(); return; }
            if ((w & 0x1FE0FC00) == 0x1A000000) { AddSubCarry(); return; }
            if ((w & 0x3FE00410) == 0x3A400000) { ConditionalCompare(); return; }
            if ((w & 0x3FE00800) == 0x1A800000) { ConditionalSelect(); return; }
            if ((w & 0x5FE00000) == 0x1AC00000) { TwoSource(); return; }
            if ((w & 0x5FE00000) == 0x5AC00000) { OneSource(); return; }
            if ((w & 0x1F000000) == 0x1B000000) { ThreeSource(); return; }
            Unsupported("data.register");
        }

        private Expr? ShiftedOperand(int width, bool allowRor)
        {
            var amount = (int)Bits(10, 6);
            if (width == 32 && amount >= 32) return null;
            var operand = X(Rm, width);
            if (amount == 0) return operand;
            var shift = Bits(22, 2) switch
            {
                0 => BinOp.Shl,
                1 => BinOp.LShr,
                2 => BinOp.AShr,
                _ => allowRor ? BinOp.Ror : (BinOp?)null,
            };
            return shift is null ? null : Op(shift.Value, operand, C((ulong)amount, width));
        }

        private void LogicalShifted()
        {
            var width = Sf;
            var right = ShiftedOperand(width, true);
            if (right is null) { Unsupported("logical.shift"); return; }
            if (Bit(21)) right = new Unary(UnOp.Not, right, width);
            var left = X(Rn, width);
            Expr result;
            switch (Bits(29, 2))
            {
                case 0: result = Op(BinOp.And, left, right); break;
                case 1: result = Rn == 31 ? right : Op(BinOp.Or, left, right); break;
                case 2: result = Op(BinOp.Xor, left, right); break;
                default:
                    result = Op(BinOp.And, left, right);
                    SetFlags(new Flags(FlagKind.Logic, result, null, width));
                    break;
            }
            SetX(Rd, result);
        }

        private void AddSubShifted()
        {
            var width = Sf;
            var right = ShiftedOperand(width, false);
            if (right is null) { Unsupported("addsub.shift"); return; }
            var subtract = Bit(30);
            var left = X(Rn, width);
            // neg/negs 是 sub 的别名，Rn 为零寄存器
            var result = subtract ? Sub(left, right) : Add(left, right);
            if (Bit(29)) SetFlags(new Flags(subtract ? FlagKind.Sub : FlagKind.Add, left, right, width));
            SetX(Rd, result);
        }

        private void AddSubExtended()
        {
            var width = Sf;
            var amount = (int)Bits(10, 3);
            if (amount > 4 || Bits(22, 2) != 0) { Unsupported("addsub.extend"); return; }
            var option = Bits(13, 3);
            var sourceWidth = (option & 3) switch { 0 => 8, 1 => 16, 2 => 32, _ => 64 };
            var signed = (option & 4) != 0;
            Expr operand = X(Rm, Math.Min(sourceWidth, width));
            if (sourceWidth < width) operand = signed ? SExt(operand, width) : ZExt(operand, width);
            if (amount != 0) operand = Op(BinOp.Shl, operand, C((ulong)amount, width));
            var subtract = Bit(30);
            var left = XSp(Rn, width);
            var result = subtract ? Sub(left, operand) : Add(left, operand);
            if (Bit(29))
            {
                SetFlags(new Flags(subtract ? FlagKind.Sub : FlagKind.Add, left, operand, width));
                SetX(Rd, result);
            }
            else SetXSp(Rd, result);
        }

        private void AddSubCarry()
        {
            var width = Sf;
            var carry = ZExt(Condition(2), width);
            var left = X(Rn, width);
            var right = Bit(30) ? new Unary(UnOp.Not, X(Rm, width), width) : X(Rm, width);
            var result = Add(Add(left, right), carry);
            if (Bit(29)) SetFlags(new Unknown("adcs.flags", 0));
            SetX(Rd, result);
        }

        private void ConditionalCompare()
        {
            var width = Sf;
            var right = Bit(11) ? C(Bits(16, 5), width) : X(Rm, width);
            var left = X(Rn, width);
            var taken = new Flags(Bit(30) ? FlagKind.Sub : FlagKind.Add, left, right, width);
            SetFlags(new ConditionalFlags(Condition(Bits(12, 4)), taken, (byte)Bits(0, 4)));
        }

        private void ConditionalSelect()
        {
            var width = Sf;
            var condition = Condition(Bits(12, 4));
            var taken = X(Rn, width);
            var other = X(Rm, width);
            Expr alternative = ((Bit(30) ? 2 : 0) | (int)Bits(10, 2)) switch
            {
                0 => other,
                1 => Add(other, C(1, width)),
                2 => new Unary(UnOp.Not, other, width),
                3 => new Unary(UnOp.Neg, other, width),
                _ => null!,
            };
            if (alternative is null) { Unsupported("csel.op2"); return; }
            SetX(Rd, new Select(condition, taken, alternative, width));
        }

        private void TwoSource()
        {
            var width = Sf;
            var left = X(Rn, width);
            var right = X(Rm, width);
            BinOp? op = Bits(10, 6) switch
            {
                2 => BinOp.UDiv,
                3 => BinOp.SDiv,
                8 => BinOp.Shl,
                9 => BinOp.LShr,
                10 => BinOp.AShr,
                11 => BinOp.Ror,
                _ => null,
            };
            if (op is null || Bit(29)) { Unsupported("data.2source"); return; }
            SetX(Rd, Op(op.Value, left, right));
        }

        private void OneSource()
        {
            var width = Sf;
            var operand = X(Rn, width);
            if (Bits(16, 5) != 0 || Bit(29)) { Unsupported("data.1source"); return; }
            UnOp? op = (Bits(10, 6), width) switch
            {
                (0, _) => UnOp.Rbit,
                (1, _) => UnOp.Bswap16,
                (2, 32) => UnOp.Bswap,
                (2, 64) => UnOp.Bswap32,
                (3, 64) => UnOp.Bswap,
                (4, _) => UnOp.Clz,
                (5, _) => UnOp.Cls,
                _ => null,
            };
            if (op is null) { Unsupported("data.1source.opcode"); return; }
            SetX(Rd, new Unary(op.Value, operand, width));
        }

        private void ThreeSource()
        {
            var op31 = Bits(21, 3);
            var subtract = Bit(15);
            if (Bits(29, 2) != 0) { Unsupported("data.3source"); return; }
            switch (op31)
            {
                case 0:
                {
                    var width = Sf;
                    var product = Op(BinOp.Mul, X(Rn, width), X(Rm, width));
                    if (Ra == 31) SetX(Rd, subtract ? new Unary(UnOp.Neg, product, width) : product);
                    else SetX(Rd, subtract ? Sub(X(Ra, width), product) : Add(X(Ra, width), product));
                    return;
                }
                case 1 or 5 when Sf == 64:
                {
                    var signed = op31 == 1;
                    Expr Widen(int reg) => signed ? SExt(X(reg, 32), 64) : ZExt(X(reg, 32), 64);
                    var product = Op(BinOp.Mul, Widen(Rn), Widen(Rm));
                    if (Ra == 31) SetX(Rd, subtract ? new Unary(UnOp.Neg, product, 64) : product);
                    else SetX(Rd, subtract ? Sub(X(Ra, 64), product) : Add(X(Ra, 64), product));
                    return;
                }
                case 2 or 6 when Sf == 64 && !subtract:
                    SetX(Rd, Op(op31 == 2 ? BinOp.MulHighS : BinOp.MulHighU, X(Rn, 64), X(Rm, 64)));
                    return;
                default:
                    Unsupported("data.3source.op31");
                    return;
            }
        }
    }
}
