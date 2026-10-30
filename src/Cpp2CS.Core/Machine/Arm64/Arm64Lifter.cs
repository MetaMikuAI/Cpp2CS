using System.Numerics;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Arm64;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>
/// ARM64 指令到 IR 的提升。按 Arm ARM 的编码表直接解码，一条指令产生若干语句；
/// 未实现的编码产生 <see cref="Opaque"/>，绝不静默丢弃。寄存器 31 按上下文区分 SP（Gpr 31）与零寄存器。
/// </summary>
public static partial class Arm64Lifter
{
    public const int Sp = 31;
    public const int Lr = 30;

    public static void Lift(ulong pc, uint w, List<Stmt> output) => new Context(pc, w, output).Run();

    private sealed partial class Context(ulong pc, uint w, List<Stmt> output)
    {
        private readonly ulong pc = pc;
        private readonly uint w = w;
        private readonly List<Stmt> output = output;

        private uint Bits(int low, int count) => (w >> low) & ((1u << count) - 1);
        private bool Bit(int index) => ((w >> index) & 1) != 0;
        private int Rd => (int)Bits(0, 5);
        private int Rn => (int)Bits(5, 5);
        private int Rm => (int)Bits(16, 5);
        private int Ra => (int)Bits(10, 5);
        private int Sf => Bit(31) ? 64 : 32;

        // ---------- 读写辅助 ----------
        private static Expr C(ulong value, int width) => Expr.C(value, width);

        /// <summary>读通用寄存器，31 为零寄存器。</summary>
        private static Expr X(int reg, int width) => reg == 31 ? C(0, width) : new Read(Storage.Gpr(reg), width);

        /// <summary>读通用寄存器，31 为 SP。</summary>
        private static Expr XSp(int reg, int width) => new Read(Storage.Gpr(reg), width);

        private static Expr V(int reg, int width) => new Read(Storage.Vec(reg), width);

        private void Emit(Stmt stmt) => output.Add(stmt);

        /// <summary>写通用寄存器，31 为零寄存器（丢弃）。</summary>
        private void SetX(int reg, Expr value)
        {
            if (reg != 31) Emit(new Assign(pc, Storage.Gpr(reg), value));
        }

        /// <summary>写通用寄存器，31 为 SP。</summary>
        private void SetXSp(int reg, Expr value) => Emit(new Assign(pc, Storage.Gpr(reg), value));

        private void SetV(int reg, Expr value) => Emit(new Assign(pc, Storage.Vec(reg), value));

        private void SetFlags(Expr flags) => Emit(new Assign(pc, Storage.Flags, flags));

        private static Expr FlagsValue => new Read(Storage.Flags, 0);

        private Expr Condition(uint code) => code switch
        {
            14 or 15 => C(1, 1),
            _ => new TestFlags(FlagsValue, (FlagCondition)code),
        };

        private void Unsupported(string what) => Emit(new Opaque(pc, $"{what} 0x{w:x8}"));

        private static Expr Add(Expr a, Expr b) => new Binary(BinOp.Add, a, b, a.Width);
        private static Expr Sub(Expr a, Expr b) => new Binary(BinOp.Sub, a, b, a.Width);
        private static Expr Op(BinOp op, Expr a, Expr b) => new Binary(op, a, b, a.Width);
        private static Expr ZExt(Expr a, int width) => a.Width == width ? a : new Ir.Convert(a.Width < width ? ConvKind.ZeroExtend : ConvKind.Truncate, a, width);
        private static Expr SExt(Expr a, int width) => a.Width == width ? a : new Ir.Convert(a.Width < width ? ConvKind.SignExtend : ConvKind.Truncate, a, width);

        /// <summary>低位截取：寄存器读直接收窄，其余用 Extract。</summary>
        private static Expr Low(Expr a, int width) => a.Width == width ? a : a switch
        {
            Read r => new Read(r.Storage, width),
            Const c => C(c.Value, width),
            _ => new Ir.Convert(ConvKind.Truncate, a, width),
        };

        private static Expr Field(Expr a, int low, int width) =>
            low == 0 ? Low(a, width) : new Extract(a, low, width);

        public void Run()
        {
            switch ((w >> 25) & 0xF)
            {
                case 0b1000 or 0b1001: DataImmediate(); break;
                case 0b1010 or 0b1011: BranchSystem(); break;
                case 0b0100 or 0b0110 or 0b1100 or 0b1110: LoadStore(); break;
                case 0b0101 or 0b1101: DataRegister(); break;
                case 0b0111 or 0b1111: FloatSimd(); break;
                default: Unsupported("unallocated"); break;
            }
        }

        // ---------- 数据处理（立即数） ----------
        private void DataImmediate()
        {
            if ((w & 0x1F000000) == 0x10000000)
            {
                var imm = (long)((int)(((Bits(5, 19) << 2) | Bits(29, 2)) << 11) >> 11);
                var value = Bit(31) ? (ulong)(((long)pc & ~0xFFFL) + (imm << 12)) : (ulong)((long)pc + imm);
                SetX(Rd, C(value, 64));
                return;
            }
            if ((w & 0x1F800000) == 0x11000000)
            {
                var width = Sf;
                var imm = (ulong)Bits(10, 12) << (Bit(22) ? 12 : 0);
                var subtract = Bit(30);
                var setFlags = Bit(29);
                var left = XSp(Rn, width);
                var right = C(imm, width);
                var result = subtract ? Sub(left, right) : Add(left, right);
                if (setFlags)
                {
                    SetFlags(new Flags(subtract ? FlagKind.Sub : FlagKind.Add, left, right, width));
                    SetX(Rd, result);
                }
                else SetXSp(Rd, result);
                return;
            }
            if ((w & 0x1F800000) == 0x12000000)
            {
                var width = Sf;
                if (width == 32 && Bit(22)) { Unsupported("logical.imm.N"); return; }
                var mask = DecodeBitMask(Bit(22), Bits(16, 6), Bits(10, 6), width);
                var left = X(Rn, width);
                var right = C(mask, width);
                switch (Bits(29, 2))
                {
                    case 0: SetXSp(Rd, Op(BinOp.And, left, right)); break;
                    case 1: SetXSp(Rd, Rn == 31 ? right : Op(BinOp.Or, left, right)); break;
                    case 2: SetXSp(Rd, Op(BinOp.Xor, left, right)); break;
                    default:
                        var result = Op(BinOp.And, left, right);
                        SetFlags(new Flags(FlagKind.Logic, result, null, width));
                        SetX(Rd, result);
                        break;
                }
                return;
            }
            if ((w & 0x1F800000) == 0x12800000)
            {
                var width = Sf;
                var shift = (int)Bits(21, 2) * 16;
                if (width == 32 && shift >= 32) { Unsupported("movewide.hw"); return; }
                var imm = (ulong)Bits(5, 16) << shift;
                switch (Bits(29, 2))
                {
                    case 0: SetX(Rd, C(~imm, width)); break;
                    case 2: SetX(Rd, C(imm, width)); break;
                    case 3: SetX(Rd, new Insert(X(Rd, width), C(Bits(5, 16), 16), shift)); break;
                    default: Unsupported("movewide.opc"); break;
                }
                return;
            }
            if ((w & 0x1F800000) == 0x13000000)
            {
                Bitfield();
                return;
            }
            if ((w & 0x7FA00000) == 0x13800000)
            {
                var width = Sf;
                var lsb = (int)Bits(10, 6);
                if (width == 32 && lsb >= 32) { Unsupported("extr.imms"); return; }
                if (Rn == Rm)
                    SetX(Rd, lsb == 0 ? X(Rn, width) : Op(BinOp.Ror, X(Rn, width), C((ulong)lsb, width)));
                else if (lsb == 0)
                    SetX(Rd, X(Rm, width));
                else
                    SetX(Rd, Op(BinOp.Or, Op(BinOp.LShr, X(Rm, width), C((ulong)lsb, width)), Op(BinOp.Shl, X(Rn, width), C((ulong)(width - lsb), width))));
                return;
            }
            Unsupported("data.immediate");
        }

        private void Bitfield()
        {
            var width = Sf;
            var immr = (int)Bits(16, 6);
            var imms = (int)Bits(10, 6);
            if (width == 32 && (immr >= 32 || imms >= 32 || Bit(22))) { Unsupported("bitfield.32"); return; }
            if (width == 64 && !Bit(22)) { Unsupported("bitfield.N"); return; }
            var source = X(Rn, width);
            switch (Bits(29, 2))
            {
                case 0: // SBFM
                    if (imms == width - 1)
                        SetX(Rd, immr == 0 ? source : Op(BinOp.AShr, source, C((ulong)immr, width)));
                    else if (imms >= immr)
                        SetX(Rd, SExt(Field(source, immr, imms - immr + 1), width));
                    else
                        SetX(Rd, Op(BinOp.Shl, SExt(Field(source, 0, imms + 1), width), C((ulong)(width - immr), width)));
                    break;
                case 2: // UBFM
                    if (imms == width - 1)
                        SetX(Rd, immr == 0 ? source : Op(BinOp.LShr, source, C((ulong)immr, width)));
                    else if (imms + 1 == immr)
                        SetX(Rd, Op(BinOp.Shl, source, C((ulong)(width - immr), width)));
                    else if (imms >= immr)
                        SetX(Rd, ZExt(Field(source, immr, imms - immr + 1), width));
                    else
                        SetX(Rd, Op(BinOp.Shl, ZExt(Field(source, 0, imms + 1), width), C((ulong)(width - immr), width)));
                    break;
                case 1: // BFM
                    if (imms >= immr)
                        SetX(Rd, new Insert(X(Rd, width), Field(source, immr, imms - immr + 1), 0));
                    else
                        SetX(Rd, new Insert(X(Rd, width), Field(source, 0, imms + 1), width - immr));
                    break;
                default: Unsupported("bitfield.opc"); break;
            }
        }

        public static ulong DecodeBitMask(bool n, uint immr, uint imms, int width)
        {
            var combined = ((n ? 1u : 0u) << 6) | (~imms & 0x3F);
            if (combined == 0) throw new InvalidDataException("逻辑立即数编码保留");
            var length = 31 - BitOperations.LeadingZeroCount(combined);
            var size = 1 << length;
            var levels = (uint)(size - 1);
            var s = (int)(imms & levels);
            var r = (int)(immr & levels);
            if (s == levels) throw new InvalidDataException("逻辑立即数编码保留");
            var element = s + 1 == 64 ? ulong.MaxValue : (1UL << (s + 1)) - 1;
            if (r != 0)
            {
                var sizeMask = size == 64 ? ulong.MaxValue : (1UL << size) - 1;
                element = ((element >> r) | (element << (size - r))) & sizeMask;
            }
            var result = 0UL;
            for (var i = 0; i < width; i += size) result |= element << i;
            return width == 64 ? result : result & 0xFFFFFFFF;
        }

        // ---------- 分支、异常、系统 ----------
        private void BranchSystem()
        {
            if ((w & 0x7C000000) == 0x14000000)
            {
                // imm26 放到最高位再算术右移，得到符号扩展后的 imm26 << 2
                var target = (ulong)((long)pc + (((long)((ulong)Bits(0, 26) << 38)) >> 36));
                if (Bit(31)) Emit(new Call(pc, CallKind.Direct, C(target, 64)));
                else Emit(new Jump(pc, target));
                return;
            }
            if ((w & 0xFF000010) == 0x54000000)
            {
                var target = Imm19Target();
                var code = Bits(0, 4);
                if (code is 14 or 15) Emit(new Jump(pc, target));
                else Emit(new Branch(pc, Condition(code), target, pc + 4));
                return;
            }
            if ((w & 0x7E000000) == 0x34000000)
            {
                var width = Sf;
                var compare = new Compare(Bit(24) ? Cond.Ne : Cond.Eq, X(Rd, width), C(0, width));
                Emit(new Branch(pc, compare, Imm19Target(), pc + 4));
                return;
            }
            if ((w & 0x7E000000) == 0x36000000)
            {
                var bit = (int)((Bits(31, 1) << 5) | Bits(19, 5));
                var width = bit >= 32 ? 64 : 32;
                var masked = Op(BinOp.And, X(Rd, width), C(1UL << bit, width));
                var target = (ulong)((long)pc + (((long)((ulong)Bits(5, 14) << 50)) >> 48));
                Emit(new Branch(pc, new Compare(Bit(24) ? Cond.Ne : Cond.Eq, masked, C(0, width)), target, pc + 4));
                return;
            }
            if ((w & 0xFE000000) == 0xD6000000)
            {
                RegisterBranch();
                return;
            }
            if ((w & 0xFFE0001F) == 0xD4200000) { Emit(new Trap(pc, $"brk #0x{Bits(5, 16):x}")); return; }
            if ((w & 0xFFE0001F) == 0xD4400000) { Emit(new Trap(pc, $"hlt #0x{Bits(5, 16):x}")); return; }
            if ((w & 0xFFE0001F) == 0xD4000001) { Emit(new Opaque(pc, $"svc #0x{Bits(5, 16):x}")); return; }
            if ((w & 0xFFFFF01F) == 0xD503201F) { Emit(new Nop(pc, $"hint #{Bits(5, 7)}")); return; }
            if ((w & 0xFFFFF09F) == 0xD503309F) { Emit(new Nop(pc, "barrier")); return; }
            if ((w & 0xFFF00000) == 0xD5300000)
            {
                var name = SystemRegister(Bits(5, 15));
                SetX(Rd, name == "nzcv" ? new Intrinsic("read_nzcv", [FlagsValue], 64) : new Intrinsic("sysreg_" + name, [], 64));
                return;
            }
            if ((w & 0xFFF00000) == 0xD5100000)
            {
                var name = SystemRegister(Bits(5, 15));
                if (name == "nzcv") SetFlags(new Intrinsic("write_nzcv", [X(Rd, 64)], 0));
                else Emit(new Opaque(pc, $"msr {name}"));
                return;
            }
            Unsupported("branch.system");
        }

        private static string SystemRegister(uint encoded) => encoded switch
        {
            0x5A10 => "nzcv",
            0x5A20 => "fpcr",
            0x5A21 => "fpsr",
            0x5E82 => "tpidr_el0",
            0x5E83 => "tpidrro_el0",
            0x5F01 => "cntvct_el0",
            0x5F02 => "cntfrq_el0",
            _ => $"s{encoded:x4}",
        };

        private ulong Imm19Target() => (ulong)((long)pc + (((long)((ulong)Bits(5, 19) << 45)) >> 43));

        private void RegisterBranch()
        {
            var opc = Bits(21, 4);
            var op2 = Bits(16, 5);
            var op3 = Bits(10, 6);
            if (op2 != 31) { Unsupported("branch.register"); return; }
            // op3: 0 普通；2/3 为带指针认证的形式（braaz 等），认证只影响合法性，不改变目标值
            if (op3 is not (0 or 2 or 3)) { Unsupported("branch.register.op3"); return; }
            var target = X(Rn, 64);
            switch (opc)
            {
                case 0 or 8: Emit(new IndirectJump(pc, target)); break;
                case 1 or 9: Emit(new Call(pc, CallKind.Indirect, target)); break;
                case 2: Emit(new Return(pc)); break;
                default: Unsupported("branch.register.opc"); break;
            }
        }
    }
}
