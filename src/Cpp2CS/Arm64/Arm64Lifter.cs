using System.Buffers.Binary;
using Cpp2CS.Ir;

namespace Cpp2CS.Arm64;

public static partial class Arm64Lifter
{
    public static LiftResult Lift(InstructionOrigin origin)
    {
        if (origin.Bytes.Length != 4 || (origin.Address & 3) != 0)
            return LiftResult.Unsupported("word", "ARM64 instruction requires four bytes and aligned address");
        var w = BinaryPrimitives.ReadUInt32LittleEndian(origin.Bytes.Span);
        if ((w & 0x1F000000) == 0x10000000) return PcRelative(new(origin, w, "adr"));
        if ((w & 0x1F800000) == 0x11000000) return AddImmediate(new(origin, w, "addsub.immediate"));
        if ((w & 0x1F800000) == 0x12000000) return LogicalImmediate(new(origin, w, "logical.immediate"));
        if ((w & 0x1F800000) == 0x12800000) return MoveWide(new(origin, w, "move.wide"));
        if ((w & 0x1F800000) == 0x13000000) return Bitfield(new(origin, w, "bitfield"));
        if ((w & 0x7FA00000) == 0x13800000) return ExtractRegister(new(origin, w, "extract"));
        if ((w & 0x1F000000) == 0x0A000000) return LogicalRegister(new(origin, w, "logical.register"));
        if ((w & 0x1F200000) == 0x0B000000) return AddRegister(new(origin, w, "addsub.shifted"), false);
        if ((w & 0x1FE00000) == 0x0B200000) return AddRegister(new(origin, w, "addsub.extended"), true);
        if ((w & 0x1FE0FC00) == 0x1A000000) return AddCarry(new(origin, w, "addsub.carry"));
        if ((w & 0x3FE00800) == 0x1A800000) return ConditionalSelect(new(origin, w, "conditional.select"));
        if ((w & 0x3FE00410) == 0x3A400000) return ConditionalCompare(new(origin, w, "conditional.compare"));
        if ((w & 0x7FE00000) == 0x1AC00000) return VariableShift(new(origin, w, ((w >> 10) & 63) is 2 or 3 ? "integer.divide" : "shift.variable"));
        if ((w & 0x7FE00000) == 0x5AC00000) return UnaryInteger(new(origin, w, "integer.unary"));
        if ((w & 0x7FE00000) == 0x1B000000) return MultiplyAdd(new(origin, w, "multiply.add"));
        if ((w & 0xFFE00000) is 0x9B200000 or 0x9BA00000) return MultiplyLong(new(origin, w, "multiply.long"));
        if ((w & 0xFFE0FC00) is 0x9B407C00 or 0x9BC07C00) return MultiplyHigh(new(origin, w, "multiply.high"));
        if ((w & 0xBFE0FC00) is 0x0E000400 or 0x0E000C00 or 0x0E002C00 or 0x0E003C00 ||
            (w & 0xFFE0FC00) is 0x5E000400 or 0x4E001C00 || (w & 0xFFE08400) == 0x6E000400)
            return SimdCopy(new(origin, w, "simd.copy"));
        if ((w & 0x9F20FC00) == 0x0E201C00) return SimdLogic(new(origin, w, "simd.logical"));
        if ((w & 0xBFFFFC00) == 0x2E205800) return SimdNot(new(origin, w, "simd.not"));
        if ((w & 0xBFE08400) == 0x2E000000) return SimdExtract(new(origin, w, "simd.extract"));
        if ((w & 0x9F20FC00) == 0x0E208400 || (w & 0xDFE0FC00) == 0x5EE08400)
            return SimdAddSubtract(new(origin, w, "simd.addsub"));
        if ((w & 0x9FF80C00) == 0x0F000400) return SimdImmediate(new(origin, w, "simd.immediate"));
        if ((w & 0x7F3E0000) is 0x1E020000 or 0x1E180000)
            return FloatFixedGeneral(new(origin, w, "fp.fixed-general"));
        if ((w & 0x8F80FC00) is 0x0F00E400 or 0x0F00FC00)
            return FloatFixedSimd(new(origin, w, "fp.fixed-simd"));
        if ((w & 0xFFFFFC00) is 0x1E260000 or 0x1E270000 or 0x9E660000 or 0x9E670000 or 0x9EAE0000 or 0x9EAF0000)
            return FloatMoveGeneral(new(origin, w, "fmov.general"));
        if ((w & 0xFF3FFC00) == 0x1E204000) return FloatMoveRegister(new(origin, w, "fmov.register"));
        if ((w & 0xFF201FE0) == 0x1E201000) return FloatMoveImmediate(new(origin, w, "fmov.immediate"));
        if ((w & 0xFF207C00) == 0x1E204000) return FloatUnary(new(origin, w, "fp.unary"));
        if ((w & 0x9FBFFC00) == 0x0EA0F800) return FloatVectorSign(new(origin, w, "fp.vector-sign"));
        if ((w & 0xFF200C00) == 0x1E200C00) return FloatConditionalSelect(new(origin, w, "fp.select"));
        if ((w & 0xFF200C00) == 0x1E200800) return FloatBinary(new(origin, w, "fp.binary"));
        if ((w & 0xFF20FC07) == 0x1E202000) return FloatCompare(new(origin, w, "fp.compare"), false);
        if ((w & 0xFF200C00) == 0x1E200400) return FloatCompare(new(origin, w, "fp.conditional-compare"), true);
        if ((w & 0x7F20FC00) == 0x1E200000) return FloatIntegerConvert(new(origin, w, "fp.integer-convert"));
        if ((w & 0x8FBFFC00) is 0x0E21D800 or 0x0E21A800 or 0x0E21B800 or 0x0EA1A800 or 0x0EA1B800 or 0x0E21C800)
            return FloatVectorConvert(new(origin, w, "fp.vector-convert"));
        if ((w & 0xBFA0FC00) is 0x0E20D400 or 0x0EA0D400 or 0x2E20DC00 or 0x2E20FC00 or 0x0E20F400 or 0x0EA0F400 or 0x0E20C400 or 0x0EA0C400 or 0x2EA0D400 or 0x2E20D400 ||
            (w & 0xFFA0FC00) == 0x7EA0D400 || (w & 0xFFBFFC00) == 0x7E30D800)
            return FloatVectorBinary(new(origin, w, "fp.vector-binary"));
        if ((w & 0xBFA0FC00) is 0x0E20E400 or 0x2E20E400 or 0x2EA0E400 ||
            (w & 0xFFA0FC00) is 0x5E20E400 or 0x7E20E400 or 0x7EA0E400)
            return FloatVectorCompare(new(origin, w, "fp.vector-compare"), false);
        if ((w & 0xBFBFFC00) is 0x0EA0D800 or 0x2EA0C800 or 0x0EA0C800 or 0x2EA0D800 or 0x0EA0E800 ||
            (w & 0xFFBFFC00) is 0x5EA0D800 or 0x7EA0C800 or 0x5EA0C800 or 0x7EA0D800 or 0x5EA0E800)
            return FloatVectorCompare(new(origin, w, "fp.vector-compare-zero"), true);
        if ((w & 0xBFFFFC00) is 0x0E617800 or 0x0E616800)
            return FloatVectorPrecision(new(origin, w, "fp.vector-precision"));
        if ((w & 0xBF00F400) == 0x0F009000 || (w & 0xFF00F400) == 0x5F009000)
            return FloatMultiplyElement(new(origin, w, "fp.multiply-element"));
        if ((w & 0xBFBFFC00) is 0x2EA1F800 or 0x0E218800 or 0x0EA18800 or 0x0E219800 or 0x0EA19800 or 0x2E218800 or 0x2E219800 or 0x2EA19800)
            return FloatVectorUnary(new(origin, w, "fp.vector-unary"));
        if ((w & 0xBF3FFC00) == 0x0E212800) return SimdNarrow(new(origin, w, "simd.narrow"));
        if ((w & 0xBF3FFC00) is 0x0E200800 or 0x2E200800 or 0x0E201800)
            return SimdReverse(new(origin, w, "simd.reverse"));
        if ((w & 0xBF20FC00) is 0x0E001800 or 0x0E005800 or 0x0E002800 or 0x0E006800 or 0x0E003800 or 0x0E007800)
            return SimdPermute(new(origin, w, "simd.permute"));
        if ((w & 0x9F20FC00) is 0x0E203400 or 0x0E203C00 or 0x0E208C00 or 0x0E204400 or 0x0E206400 or 0x0E206C00 ||
            (w & 0xDFE0FC00) is 0x5EE03400 or 0x5EE03C00 or 0x5EE08C00 or 0x5EE04400 || (w & 0xBF20FC00) == 0x0E209C00)
            return SimdIntegerBinary(new(origin, w, "simd.integer-binary"));
        if ((w & 0x9F3FFC00) is 0x0E208800 or 0x0E209800 or 0x0E20B800 || (w & 0xBF3FFC00) == 0x0E20A800 ||
            (w & 0xDFFFFC00) is 0x5EE08800 or 0x5EE09800 or 0x5EE0B800 || (w & 0xFFFFFC00) == 0x5EE0A800)
            return SimdIntegerUnary(new(origin, w, "simd.integer-unary"));
        if ((w & 0xBF3FFC00) == 0x0E31B800 || (w & 0xFFFFFC00) == 0x5EF1B800 || (w & 0xBF20FC00) == 0x0E20BC00)
            return SimdAddReduce(new(origin, w, "simd.add-reduce"));
        if ((w & 0xBF80FC00) is 0x0F005400 or 0x0F000400 or 0x2F000400 or 0x0F00A400 or 0x2F00A400 or 0x0F008400 ||
            (w & 0xFF80FC00) is 0x5F005400 or 0x5F000400 or 0x7F000400)
            return SimdShiftImmediate(new(origin, w, "simd.shift-immediate"));
        if ((w & 0xBF00F400) == 0x0F008000) return SimdMultiplyElement(new(origin, w, "simd.multiply-element"));
        if ((w & 0x9F20FC00) is 0x0E201000 or 0x0E203000) return SimdAddWide(new(origin, w, "simd.add-wide"));
        if ((w & 0x7C000000) == 0x14000000) return DirectBranch(new(origin, w, "branch.direct"));
        if ((w & 0xFF000010) == 0x54000000) return ConditionalBranch(new(origin, w, "branch.condition"));
        if ((w & 0x7E000000) == 0x34000000) return CompareBranch(new(origin, w, "branch.zero"));
        if ((w & 0x7E000000) == 0x36000000) return TestBranch(new(origin, w, "branch.bit"));
        if ((w & 0xFFFFFC1F) is 0xD61F0000 or 0xD63F0000 or 0xD65F0000)
            return RegisterBranch(new(origin, w, "branch.register"));
        if ((w & 0x3B000000) == 0x39000000) return SingleMemory(new(origin, w, "memory.unsigned"), 0);
        if ((w & 0x3B200000) == 0x38000000) return SingleMemory(new(origin, w, "memory.unscaled"), 1);
        if ((w & 0x3B200C00) == 0x38200800) return SingleMemory(new(origin, w, "memory.register"), 2);
        if ((w & 0x3A000000) == 0x28000000) return PairMemory(new(origin, w, "memory.pair"));
        if ((w & 0x3B000000) == 0x18000000) return LiteralMemory(new(origin, w, "memory.literal"));
        if ((w & 0xBF000000) == 0x0C000000) return StructureMultiple(new(origin, w, "memory.structure-multiple"));
        if ((w & 0xBF000000) == 0x0D000000) return StructureSingle(new(origin, w, "memory.structure-single"));
        if ((w & 0xFFFFFFE0) is 0xD53B4200 or 0xD51B4200) return NzcvTransfer(new(origin, w, "nzcv.transfer"));
        if ((w & 0xFFDFFFE0) is 0xD51B4400 or 0xD51B4420 or 0xD51BD040)
            return SystemRegister(new(origin, w, "system.register"));
        if ((w & 0xFFE0001F) == 0xD4200000)
            return new Context(origin, w, "brk").End(MirExit.Trap($"arm64.BRK.0x{(w >> 5) & 0xFFFF:X4}", origin.Address));
        if (w == 0xD503201F) return new Context(origin, w, "nop").Done();
        return LiftResult.Unsupported($"word.{w:x8}", "Encoding has no implemented semantic rule");
    }

    private sealed class Context(InstructionOrigin origin, uint word, string form)
    {
        public readonly InstructionOrigin Origin = origin;
        public readonly uint Word = word;
        public readonly string Form = form;
        public readonly MirBuilder B = new(Architecture.Arm64, origin, "arm64." + form);
        public int Width => (Word & 0x80000000) != 0 ? 64 : 32;
        public int Rd => Field(0, 5);
        public int Rn => Field(5, 5);
        public int Rm => Field(16, 5);
        public int Field(int low, int bits) => (int)((Word >> low) & ((1u << bits) - 1));
        public bool Bit(int bit) => ((Word >> bit) & 1) != 0;
        public Value C(int width, ulong value) => B.Const(width, value);
        public Value Read(int register, int width, bool sp = false)
        {
            if (register == 31 && !sp) return C(width, 0);
            var value = B.Read(register == 31 ? "sp" : $"x{register}", 64);
            return width == 64 ? value : B.Trunc(value, width);
        }
        public void Write(int register, Value value, bool sp = false)
        {
            if (register == 31 && !sp) return;
            B.Write(register == 31 ? "sp" : $"x{register}", value.Width == 64 ? value : B.Zext(value, 64));
        }
        public Value ReadVector(int register, int width)
        {
            var value = B.Read($"v{register}", 128);
            return width == 128 ? value : B.Trunc(value, width);
        }
        public void WriteVector(int register, Value value) => B.Write($"v{register}", value.Width == 128 ? value : B.Zext(value, 128));
        public Value Flag(string flag) => B.Read(flag, 1);
        public Value Address(long delta) => C(64, unchecked(Origin.Address + (ulong)delta));
        public LiftResult Done() => LiftResult.Supported(B.Finish(MirExit.Next(unchecked(Origin.Address + 4))));
        public LiftResult End(MirExit exit) => LiftResult.Supported(B.Finish(exit));
        public LiftResult Reject(string reason) => LiftResult.Unsupported(Form, reason);
        public void Nz(Value value)
        {
            B.Write("n", B.Extract(value, value.Width - 1, 1));
            B.Write("z", B.Eq(value, C(value.Width, 0)));
        }
        public Value Add(Value left, Value right, bool subtract, Value carry, bool flags)
        {
            var sum = Arithmetic.AddWithCarry(B, left, subtract ? B.Not(right) : right, carry);
            if (flags)
            {
                Nz(sum.Result);
                B.Write("c", sum.Carry);
                B.Write("v", sum.Overflow);
            }
            return sum.Result;
        }
        public Value Condition(int condition)
        {
            if (condition >= 14) return C(1, 1);
            Value value = (condition >> 1) switch
            {
                0 => Flag("z"),
                1 => Flag("c"),
                2 => Flag("n"),
                3 => Flag("v"),
                4 => B.And(Flag("c"), B.BoolNot(Flag("z"))),
                5 => B.Eq(Flag("n"), Flag("v")),
                6 => B.And(B.BoolNot(Flag("z")), B.Eq(Flag("n"), Flag("v"))),
                _ => throw new InvalidOperationException("Condition code out of range")
            };
            return (condition & 1) != 0 ? B.BoolNot(value) : value;
        }
        public Value Shift(Value value, int kind, int amount)
        {
            if (amount == 0) return value;
            var count = C(value.Width, (ulong)amount);
            return kind switch
            {
                0 => B.Shl(value, count),
                1 => B.Shr(value, count),
                2 => B.Sar(value, count),
                3 => B.Or(B.Shr(value, count), B.Shl(value, C(value.Width, (ulong)(value.Width - amount)))),
                _ => throw new InvalidOperationException("Shift kind out of range")
            };
        }
    }

    private static long SignExtend(ulong value, int bits) => (long)(value << (64 - bits)) >> (64 - bits);
    private static ulong Mask(int bits) => bits == 64 ? ulong.MaxValue : (1UL << bits) - 1;

    private static LiftResult PcRelative(Context c)
    {
        var immediate = SignExtend(((ulong)c.Field(5, 19) << 2) | (uint)c.Field(29, 2), 21);
        var address = c.Bit(31)
            ? unchecked((c.Origin.Address & ~0xFFFUL) + (ulong)(immediate << 12))
            : unchecked(c.Origin.Address + (ulong)immediate);
        c.Write(c.Rd, c.C(64, address));
        return c.Done();
    }

    private static LiftResult AddImmediate(Context c)
    {
        var left = c.Read(c.Rn, c.Width, true);
        var right = c.C(c.Width, (ulong)c.Field(10, 12) << (c.Bit(22) ? 12 : 0));
        var result = c.Add(left, right, c.Bit(30), c.C(1, c.Bit(30) ? 1UL : 0UL), c.Bit(29));
        c.Write(c.Rd, result, !c.Bit(29));
        return c.Done();
    }

    private static LiftResult AddRegister(Context c, bool extended)
    {
        var shift = c.Field(10, extended ? 3 : 6);
        var kind = c.Field(22, 2);
        if (extended && (shift > 4 || (c.Width == 32 && (c.Field(13, 3) & 3) == 3)))
            return c.Reject("Unsupported or reserved extended-register form");
        if (!extended && (kind == 3 || shift >= c.Width)) return c.Reject("Reserved shifted-register encoding");
        var left = c.Read(c.Rn, c.Width, extended);
        Value right;
        if (extended)
        {
            var option = c.Field(13, 3);
            var sourceWidth = 8 << (option & 3);
            right = c.Read(c.Rm, sourceWidth);
            right = sourceWidth == c.Width ? right : ((option & 4) != 0 ? c.B.Sext(right, c.Width) : c.B.Zext(right, c.Width));
            right = c.Shift(right, 0, shift);
        }
        else right = c.Shift(c.Read(c.Rm, c.Width), kind, shift);
        var result = c.Add(left, right, c.Bit(30), c.C(1, c.Bit(30) ? 1UL : 0UL), c.Bit(29));
        c.Write(c.Rd, result, extended && !c.Bit(29));
        return c.Done();
    }

    private static LiftResult AddCarry(Context c)
    {
        var left = c.Read(c.Rn, c.Width);
        var right = c.Read(c.Rm, c.Width);
        var carry = c.Flag("c");
        c.Write(c.Rd, c.Add(left, right, c.Bit(30), carry, c.Bit(29)));
        return c.Done();
    }

    private static LiftResult MoveWide(Context c)
    {
        var opcode = c.Field(29, 2);
        var shift = c.Field(21, 2) * 16;
        if (opcode == 1 || shift >= c.Width) return c.Reject("Reserved move-wide encoding");
        var immediate = (ulong)c.Field(5, 16) << shift;
        Value result;
        if (opcode == 0) result = c.C(c.Width, ~immediate & Mask(c.Width));
        else if (opcode == 2) result = c.C(c.Width, immediate);
        else result = c.B.Or(c.B.And(c.Read(c.Rd, c.Width), c.C(c.Width, ~(0xFFFFUL << shift) & Mask(c.Width))), c.C(c.Width, immediate));
        c.Write(c.Rd, result);
        return c.Done();
    }

    private static LiftResult LogicalRegister(Context c)
    {
        var amount = c.Field(10, 6);
        if (amount >= c.Width) return c.Reject("Reserved 32-bit shift amount");
        var left = c.Read(c.Rn, c.Width);
        var right = c.Shift(c.Read(c.Rm, c.Width), c.Field(22, 2), amount);
        if (c.Bit(21)) right = c.B.Not(right);
        return Logical(c, left, right);
    }

    private static LiftResult LogicalImmediate(Context c)
    {
        if (!DecodeMasks(c, true, out var writeMask, out _)) return c.Reject("Reserved logical immediate bitmask");
        return Logical(c, c.Read(c.Rn, c.Width), c.C(c.Width, writeMask));
    }

    private static LiftResult Logical(Context c, Value left, Value right)
    {
        var opcode = c.Field(29, 2);
        var result = opcode switch { 0 or 3 => c.B.And(left, right), 1 => c.B.Or(left, right), 2 => c.B.Xor(left, right), _ => throw new InvalidOperationException() };
        c.Write(c.Rd, result, c.Form == "logical.immediate" && opcode != 3);
        if (opcode == 3)
        {
            c.Nz(result);
            c.B.Write("c", c.C(1, 0));
            c.B.Write("v", c.C(1, 0));
        }
        return c.Done();
    }

    private static bool DecodeMasks(Context c, bool immediate, out ulong writeMask, out ulong topMask)
    {
        writeMask = topMask = 0;
        var n = c.Field(22, 1);
        var s = c.Field(10, 6);
        var r = c.Field(16, 6);
        if (c.Width == 32 && n != 0) return false;
        var pattern = (n << 6) | ((~s) & 63);
        var length = 6;
        while (length >= 0 && (pattern & (1 << length)) == 0) length--;
        if (length < 1) return false;
        var levels = (1 << length) - 1;
        if (immediate && (s & levels) == levels) return false;
        s &= levels;
        r &= levels;
        var size = 1 << length;
        var element = Mask(s + 1);
        var rotated = r == 0 ? element : ((element >> r) | (element << (size - r))) & Mask(size);
        var top = Mask(((s - r) & levels) + 1);
        for (var offset = 0; offset < c.Width; offset += size)
        {
            writeMask |= rotated << offset;
            topMask |= top << offset;
        }
        return true;
    }

    private static LiftResult Bitfield(Context c)
    {
        var opcode = c.Field(29, 2);
        if (opcode == 3 || c.Field(22, 1) != (c.Width == 64 ? 1 : 0) || c.Field(10, 6) >= c.Width || c.Field(16, 6) >= c.Width)
            return c.Reject("Reserved bitfield encoding");
        if (!DecodeMasks(c, false, out var writeMask, out var topMask)) return c.Reject("Invalid bitfield masks");
        var source = c.Read(c.Rn, c.Width);
        var rotated = c.Shift(source, 3, c.Field(16, 6));
        var bottom = c.B.And(rotated, c.C(c.Width, writeMask));
        Value top;
        if (opcode == 1)
        {
            var old = c.Read(c.Rd, c.Width);
            bottom = c.B.Or(c.B.And(old, c.C(c.Width, ~writeMask & Mask(c.Width))), bottom);
            top = old;
        }
        else if (opcode == 0) top = c.B.Sext(c.B.Extract(source, c.Field(10, 6), 1), c.Width);
        else top = c.C(c.Width, 0);
        c.Write(c.Rd, c.B.Or(c.B.And(top, c.C(c.Width, ~topMask & Mask(c.Width))), c.B.And(bottom, c.C(c.Width, topMask))));
        return c.Done();
    }

    private static LiftResult ExtractRegister(Context c)
    {
        var amount = c.Field(10, 6);
        if (c.Field(22, 1) != (c.Width == 64 ? 1 : 0) || amount >= c.Width) return c.Reject("Reserved extract encoding");
        var low = c.Read(c.Rm, c.Width);
        var high = c.Read(c.Rn, c.Width);
        var result = amount == 0 ? low : c.B.Or(c.B.Shr(low, c.C(c.Width, (ulong)amount)), c.B.Shl(high, c.C(c.Width, (ulong)(c.Width - amount))));
        c.Write(c.Rd, result);
        return c.Done();
    }
}
