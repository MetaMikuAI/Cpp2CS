using System.Numerics;

namespace Cpp2CS.Target;

public enum Form
{
    Unknown, Nop, Trap, Return, BranchRegister, CallRegister, Branch, Call, Condition, CompareBranch, TestBranch,
    Address, Wide, Immediate, Shifted, Extended, Logical, Mask, Bitfield, Select, Multiply, Binary, Unary,
    Memory, Pair, Literal, Thread, FloatBinary, FloatUnary, FloatCompare, FloatMove, FloatSelect, Fused, LongMultiply, Extract, VectorImmediate, VectorOr, FloatImmediate, Convert
}

/// <summary>DDI 0487 的 A64 基本指令和标量浮点编码。立即数在解码时完成符号扩展与比例换算。</summary>
public readonly record struct Instruction(Form Form, string Name, int Width = 64, int D = 31, int N = 31,
    int M = 31, int A = 31, long Imm = 0, int Mode = 0, int Shift = 0, int Size = 0, bool Vector = false)
{
    public bool Conditional => Form is Form.Condition or Form.CompareBranch or Form.TestBranch;
    public bool IsCall => Form is Form.Call or Form.CallRegister;
    public ulong Destination(ulong pc) => unchecked(pc + (ulong)Imm);
}

public static class Decoder
{
    static readonly string[] arithmetic = ["add", "adds", "sub", "subs"];
    static readonly string[] logical = ["and", "bic", "orr", "orn", "eor", "eon", "ands", "bics"];
    static readonly string[] selection = ["csel", "csinc", "csinv", "csneg"];
    static readonly string[] floating = ["fmul", "fdiv", "fadd", "fsub", "fmax", "fmin", "fmaxnm", "fminnm", "fnmul"];
    static long Signed(uint v, int size) => (int)(v << (32 - size)) >> (32 - size);

    public static Instruction Decode(uint word)
    {
        int F(int lo, int bits) => (int)((word >> lo) & ((1u << bits) - 1));
        bool Is(uint mask, uint bits) => (word & mask) == bits;
        int d = F(0, 5), n = F(5, 5), a = F(10, 5), m = F(16, 5), w = F(31, 1) == 0 ? 32 : 64;
        int opc = F(29, 2), shift = F(10, 6), mode = F(22, 2);
        if (word == 0xd503201f) return new(Form.Nop, "nop");
        if (Is(0xffe0001f, 0xd4200000)) return new(Form.Trap, "brk", Imm: F(5, 16));
        if (Is(0xffff0000, 0)) return new(Form.Trap, "udf", Imm: F(0, 16));
        if (Is(0xfffffc1f, 0xd65f0000)) return new(Form.Return, "ret", N: n);
        if (Is(0xfffffc1f, 0xd61f0000)) return new(Form.BranchRegister, "br", N: n);
        if (Is(0xfffffc1f, 0xd63f0000)) return new(Form.CallRegister, "blr", N: n);
        if (Is(0x7c000000, 0x14000000))
            return new(w == 64 ? Form.Call : Form.Branch, w == 64 ? "bl" : "b", Imm: Signed(word, 26) * 4);
        if (Is(0xff000010, 0x54000000))
            return new(Form.Condition, "b", Imm: Signed(word >> 5, 19) * 4, Mode: F(0, 4));
        if (Is(0x7e000000, 0x34000000))
            return new(Form.CompareBranch, F(24, 1) == 0 ? "cbz" : "cbnz", w, d, Imm: Signed(word >> 5, 19) * 4);
        if (Is(0x7e000000, 0x36000000))
            return new(Form.TestBranch, F(24, 1) == 0 ? "tbz" : "tbnz", w, d, Imm: Signed(word >> 5, 14) * 4, Shift: F(19, 5) + F(31, 1) * 32);
        if (Is(0x1f000000, 0x10000000))
            return new(Form.Address, w == 64 ? "adrp" : "adr", 64, d, Imm: Signed((uint)(F(5, 19) << 2 | F(29, 2)), 21) * (w == 64 ? 4096 : 1));
        if (Is(0x1f800000, 0x12800000) && opc != 1 && F(21, 2) * 16 < w)
            return new(Form.Wide, opc switch { 0 => "movn", 2 => "movz", _ => "movk" }, w, d, Imm: F(5, 16), Shift: F(21, 2) * 16);
        if (Is(0x1f800000, 0x11000000))
            return new(Form.Immediate, arithmetic[opc], w, d, n, Imm: F(10, 12), Shift: F(22, 1) * 12);
        if (Is(0x1f200000, 0x0b000000) && mode != 3 && shift < w)
            return new(Form.Shifted, arithmetic[opc], w, d, n, m, Mode: mode, Shift: shift);
        if (Is(0x1fe00000, 0x0b200000) && F(10, 3) <= 4)
            return new(Form.Extended, arithmetic[opc], w, d, n, m, Mode: F(13, 3), Shift: F(10, 3));
        if (Is(0x1f000000, 0x0a000000) && shift < w)
            return new(Form.Logical, logical[opc * 2 + F(21, 1)], w, d, n, m, Mode: mode, Shift: shift);
        if (Is(0x1f800000, 0x12000000) && (w == 64 || F(22, 1) == 0))
        {
            int s = F(10, 6), r = F(16, 6);
            int len = BitOperations.Log2((uint)(F(22, 1) << 6 | (63 - s)));
            int element = 1 << len;
            if (element < 2 || (s & (element - 1)) == element - 1) return default;
            ulong bits = (1ul << ((s & (element - 1)) + 1)) - 1;
            int rot = r & (element - 1);
            bits = (bits >> rot | bits << (element - rot)) & (ulong.MaxValue >> (64 - element));
            for (int filled = element; filled < w; filled *= 2) bits |= bits << filled;
            return new(Form.Mask, logical[opc * 2], w, d, n, Imm: (long)bits);
        }
        if (Is(0x1f800000, 0x13000000) && opc != 3 && F(22, 1) == F(31, 1) && F(16, 6) < w && shift < w)
            return new(Form.Bitfield, opc switch { 0 => "sbfm", 1 => "bfm", _ => "ubfm" }, w, d, n, Imm: F(16, 6), Shift: shift);
        if (Is(0x3fe00800, 0x1a800000))
            return new(Form.Select, selection[F(30, 1) * 2 + F(10, 1)], w, d, n, m, Mode: F(12, 4));
        if (Is(0x7fe00000, 0x1b000000))
            return new(Form.Multiply, F(15, 1) == 0 ? "madd" : "msub", w, d, n, m, a);
        if (Is(0xffe0fc00, 0x9b407c00) || Is(0xffe0fc00, 0x9bc07c00))
            return new(Form.Binary, F(23, 1) == 0 ? "smulh" : "umulh", 64, d, n, m);
        if (Is(0x7fe00000, 0x1ac00000))
        {
            string? name = F(10, 6) switch { 2 => "udiv", 3 => "sdiv", 8 => "lslv", 9 => "lsrv", 10 => "asrv", 11 => "rorv", _ => null };
            if (name != null) return new(Form.Binary, name, w, d, n, m);
        }
        if (Is(0x7ffff000, 0x5ac01000) && F(10, 2) == 0) return new(Form.Unary, "clz", w, d, n);
        if (Is(0xffffffe0, 0xd53bd040)) return new(Form.Thread, "mrs", 64, d);
        int sz = F(30, 2), op = F(22, 2);
        bool vec = F(26, 1) != 0;
        if (Is(0x3a000000, 0x28000000))
        {
            bool load = F(22, 1) != 0;
            int indexing = F(23, 2);
            if (sz == 3 || (!vec && sz == 1 && (!load || indexing == 0))) return default;
            int width = vec ? 32 << sz : sz == 2 ? 64 : 32;
            string name = (!vec && sz == 1) ? "ldpsw" : indexing == 0 ? (load ? "ldnp" : "stnp") : (load ? "ldp" : "stp");
            if ((load && d == a) || (!vec && indexing is 1 or 3 && n != 31 && (n == d || n == a))) return default;
            return new(Form.Pair, name, !vec && sz == 1 ? 64 : width, d, n, A: a, Imm: Signed(word >> 15, 7) * (width / 8), Mode: indexing, Size: width, Vector: vec);
        }
        if (Is(0x3b000000, 0x18000000) && sz != 3)
            return new(Form.Literal, !vec && sz == 2 ? "ldrsw" : "ldr", vec ? 32 << sz : sz == 0 ? 32 : 64, d,
                Imm: Signed(word >> 5, 19) * 4, Size: vec ? 32 << sz : sz == 1 ? 64 : 32, Vector: vec);
        bool scaled = Is(0x3b000000, 0x39000000), indexed = Is(0x3b200000, 0x38000000),
            reg = Is(0x3b200c00, 0x38200800);
        if (scaled || indexed || reg)
        {
            if ((vec && op >= 2 && sz != 0) || (!vec && (op == 2 && sz == 3 || op == 3 && sz >= 2))) return default;
            int index = indexed ? F(10, 2) : 0;
            if (index == 2 || (reg && (F(13, 3) & 2) == 0)) return default;
            if (!vec && index != 0 && n != 31 && n == d) return default;
            int size = vec && op >= 2 ? 128 : 8 << sz;
            bool load = vec ? (op & 1) != 0 : op != 0;
            string name = load ? "ldr" : "str";
            if (indexed && index == 0) name = load ? "ldur" : "stur";
            if (!vec) name += (op >= 2 ? "s" : "") + (size switch { 8 => "b", 16 => "h", 32 when op >= 2 => "w", _ => "" });
            int width = vec ? size : op == 2 || sz == 3 ? 64 : 32;
            return new(Form.Memory, name, width, d, n, m, Imm: scaled ? F(10, 12) * (size / 8) : indexed ? Signed(word >> 12, 9) : 0,
                Mode: reg ? 4 + F(13, 3) : index, Shift: reg && F(12, 1) != 0 ? BitOperations.Log2((uint)(size / 8)) : 0, Size: size, Vector: vec);
        }
        int fw = 32 << F(22, 1);
        if (Is(0xffa00c00, 0x1e200800) && F(12, 4) < floating.Length)
            return new(Form.FloatBinary, floating[F(12, 4)], fw, d, n, m);
        if (Is(0xffa0fc07, 0x1e202000) && (F(3, 1) == 0 || m == 0))
            return new(Form.FloatCompare, F(4, 1) == 0 ? "fcmp" : "fcmpe", fw, N: n, M: m, Mode: F(3, 1));
        if (Is(0xffa00c00, 0x1e200c00)) return new(Form.FloatSelect, "fcsel", fw, d, n, m, Mode: F(12, 4));
        if (Is(0xff800000, 0x1f000000))
            return new(Form.Fused, (F(21, 1), F(15, 1)) switch { (0, 0) => "fmadd", (0, 1) => "fmsub", (1, 0) => "fnmadd", _ => "fnmsub" }, fw, d, n, m, a);
        if (Is(0xffa07c00, 0x1e204000))
        {
            string? name = F(15, 6) switch { 0 => "fmov", 1 => "fabs", 2 => "fneg", 3 => "fsqrt", 8 => "frintn", 9 => "frintp", 10 => "frintm", 11 => "frintz", _ => null };
            if (name != null) return new(Form.FloatUnary, name, fw, d, n);
        }
        if (Is(0x7fbefc00, 0x1e260000) && F(31, 1) == F(22, 1) && F(16, 1) <= 1)
            return new(Form.FloatMove, "fmov", fw, d, n, Mode: F(16, 1));
        if (Is(0xff600000, 0x9b200000))
        {
            string name = (F(23, 1), F(15, 1)) switch { (0, 0) => "smaddl", (0, 1) => "smsubl", (1, 0) => "umaddl", _ => "umsubl" };
            return new(Form.LongMultiply, name, 64, d, n, m, a);
        }
        if (Is(0x7fa00000, 0x13800000) && F(22, 1) == F(31, 1) && shift < w)
            return new(Form.Extract, "extr", w, d, n, m, Shift: shift);
        if (Is(0xbfe0fc00, 0x0ea01c00))
            return new(Form.VectorOr, "orr", 64 << F(30, 1), d, n, m);
        if (Is(0x9ff80c00, 0x0f000400))
        {
            int cmode = F(12, 4), opbit = F(29, 1);
            int immediate = F(16, 3) << 5 | F(5, 5);
            if (cmode == 14 && opbit == 1)
            {
                ulong pattern = 0;
                for (int bit = 0; bit < 8; bit++)
                    if ((immediate & (1 << bit)) != 0) pattern |= 0xfful << (8 * bit);
                return new(Form.VectorImmediate, "movi", 64 << F(30, 1), d, Imm: (long)pattern, Size: 64);
            }
            if (cmode == 14 || cmode < 12 && (cmode & 1) == 0)
            {
                int element = cmode == 14 ? 8 : cmode < 8 ? 32 : 16;
                return new(Form.VectorImmediate, opbit == 0 ? "movi" : "mvni", 64 << F(30, 1), d, Imm: immediate,
                    Shift: element == 8 ? 0 : 8 * ((cmode >> 1) % (element / 8)), Size: element);
            }
        }
        if (Is(0xffa01fe0, 0x1e201000))
        {
            int literal = F(13, 8);
            double number = Math.ScaleB(1.0 + (literal & 15) / 16.0, ((literal >> 4) & 7) ^ 4);
            number = Math.ScaleB(number, -3) * ((literal & 128) == 0 ? 1 : -1);
            return new(Form.FloatImmediate, "fmov", fw, d, Imm: fw == 32 ? BitConverter.SingleToInt32Bits((float)number) : BitConverter.DoubleToInt64Bits(number));
        }
        if (Is(0x7fbeFC00, 0x1e220000) || Is(0x7fbefc00, 0x1e380000))
        {
            bool fromFloat = F(19, 1) != 0;
            string name = fromFloat ? (F(16, 1) == 0 ? "fcvtzs" : "fcvtzu") : (F(16, 1) == 0 ? "scvtf" : "ucvtf");
            return new(Form.Convert, name, fromFloat ? w : fw, d, n, Size: fromFloat ? fw : w);
        }
        if (Is(0xfffffc00, 0x1e22c000) || Is(0xfffffc00, 0x1e624000))
            return new(Form.Convert, "fcvt", fw == 32 ? 64 : 32, d, n, Size: fw);
        return default;
    }
}
