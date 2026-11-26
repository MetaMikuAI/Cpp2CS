using System.Numerics;

namespace Cpp2CS.Target;

/// <summary>DDI 0487 C6、C7：条件比较、位重排及 Advanced SIMD。Width 为结果位宽，Size 为元素位宽。</summary>
internal static class SimdDecoder
{
    public static Instruction Decode(uint word)
    {
        int Field(int lo, int bits) => (int)(word >> lo) & ((1 << bits) - 1);
        bool Is(uint mask, uint code) => (word & mask) == code;
        int d = Field(0, 5), n = Field(5, 5), m = Field(16, 5), q = Field(30, 1);
        int width = 64 << q, size = 8 << Field(22, 2), fp = 32 << Field(22, 1);
        int gpr = 32 << Field(31, 1), cond = Field(12, 4);
        if (Is(0x3fe00410, 0x3a400000))
            return new(Form.ConditionalCompare, q == 1 ? "ccmp" : "ccmn", gpr, N: n, M: m,
                Imm: d & 15, Mode: cond, Vector: Field(11, 1) != 0);
        if (Is(0xffa00c00, 0x1e200400))
            return new(Form.FloatConditionalCompare, d < 16 ? "fccmp" : "fccmpe", fp, N: n, M: m, Imm: d & 15, Mode: cond);
        if (Is(0x7ffff000, 0x5ac00000))
        {
            int op = Field(10, 2);
            if (op == 3 && gpr == 32) return default;
            string name = op switch { 0 => "rbit", 1 => "rev16", 2 when gpr == 64 => "rev32", _ => "rev" };
            return new(Form.Reverse, name, gpr, d, n, Size: op == 0 ? gpr : 8 << op);
        }
        if (Is(0x7fbefc00, 0x1e280000) || Is(0x7fbefc00, 0x1e300000))
            return new(Form.RoundConvert, "fcvt" + (Field(20, 1) == 0 ? "p" : "m") + (Field(16, 1) == 0 ? "s" : "u"),
                gpr, d, n, Size: fp);
        if (Is(0x7fbe0000, 0x1e180000) && (gpr == 64 || Field(15, 1) != 0))
            return new(Form.RoundConvert, Field(16, 1) == 0 ? "fcvtzs" : "fcvtzu", gpr, d, n, Shift: 64 - Field(10, 6), Size: fp);

        Instruction Binary(string name, int element) => new(Form.SimdBinary, name, width, d, n, m, Size: element);
        string? opName = (word & 0xbf20fc00) switch
        {
            0x0e208400 => "add", 0x2e208400 => "sub", 0x0e209c00 => "mul", 0x2e208c00 => "cmeq",
            0x0e203400 => "cmgt", 0x2e203400 => "cmhi", 0x2e203c00 => "cmhs", 0x0e206400 => "smax",
            0x0e206c00 => "smin", 0x2e204400 => "ushl", _ => null
        };
        if (opName != null && (size < 64 || q == 1 && opName is not ("mul" or "smax" or "smin")))
            return Binary(opName, size);
        opName = (word & 0xbfe0fc00) switch
        {
            0x0e201c00 => "and", 0x0e601c00 => "bic", 0x0ee01c00 => "orn", 0x2e201c00 => "eor",
            0x2e601c00 => "bsl", 0x2ea01c00 => "bit", 0x2ee01c00 => "bif", _ => null
        };
        if (opName != null) return new(Form.SimdBits, opName, width, d, n, m, Size: 8);
        opName = (word & 0xbfa0fc00) switch
        {
            0x0e20d400 => "fadd", 0x0ea0d400 => "fsub", 0x2e20dc00 => "fmul", 0x2e20fc00 => "fdiv",
            0x0e20e400 => "fcmeq", 0x2ea0e400 => "fcmgt", 0x0ea0f400 => "fmin", 0x0e20c400 => "fmaxnm",
            0x2ea0d400 => "fabd", _ => null
        };
        if (opName != null && (q == 1 || fp == 32)) return Binary(opName, fp);
        if (Is(0xffa0fc00, 0x7ea0d400)) return new(Form.SimdBinary, "fabd", fp, d, n, m, Size: fp);
        bool scalar = Field(28, 1) == 1;
        opName = (word & 0xbfbffc00) switch
        {
            0x0ea0f800 => "fabs", 0x2ea0f800 => "fneg", 0x0ea0d800 => "fcmeq", 0x2ea0c800 => "fcmge",
            0x0ea0c800 => "fcmgt", 0x0ea0e800 => "fcmlt", 0x0e21d800 => "scvtf", 0x2e21d800 => "ucvtf",
            0x0ea1b800 => "fcvtzs", 0x0e219800 => "frintm", 0x2ea1f800 => "fsqrt", _ => null
        };
        if (opName != null && (fp == 32 || q == 1)) return new(Form.SimdUnary, opName, width, d, n, Size: fp);
        if (Is(0xdfbffc00, 0x5e21d800))
            return new(Form.SimdUnary, Field(29, 1) == 0 ? "scvtf" : "ucvtf", fp, d, n, Size: fp);
        if (Is(0xbffffc00, 0x2e205800) || Is(0xbffffc00, 0x0e205800))
            return new(Form.SimdUnary, Field(29, 1) == 1 ? "mvn" : "cnt", width, d, n, Size: 8);
        if (Is(0xbf3ffc00, 0x2e20b800) && (q == 1 || size != 64))
            return new(Form.SimdUnary, "neg", width, d, n, Size: size);
        if (Is(0xbf3ffc00, 0x0e200800) && size < 64)
            return new(Form.SimdUnary, "rev64", width, d, n, Size: size);

        if (Is(0xafc0f400, 0x0f809000) || Is(0xafe0f400, 0x0fc09000) || Is(0xbf00f400, 0x0f008000))
        {
            bool integer = Field(12, 4) == 8;
            int element = integer ? size : fp;
            if (integer && element is not (16 or 32) || scalar && (integer || q == 0) || !scalar && q == 0 && element == 64) return default;
            int lane = Field(11, 1) * (64 / element) + (element <= 32 ? Field(21, 1) * (32 / element) : 0);
            if (element == 16) { lane += m >> 4; m &= 15; }
            return new(Form.SimdIndexed, integer ? "mul" : "fmul", scalar ? element : width, d, n, m, Shift: lane, Size: element);
        }
        if (Is(0x9fe08400, 0x0e000400) || Is(0xffe0fc00, 0x5e000400))
        {
            int low = BitOperations.TrailingZeroCount((uint)m);
            if (low > 3) return default;
            int element = 8 << low, index = m >> (low + 1), imm4 = Field(11, 4);
            int kind = Field(29, 1) == 1 ? (q == 1 ? 4 : -1) : (imm4, scalar) switch
            {
                (0, false) => 1, (0, true) => 2, (1, false) when m == 1 << low => 0,
                (3, false) when q == 1 => 3, (7, false) when (element == 64) == (q == 1) => 5, _ => -1
            };
            if (kind < 0 || kind < 2 && q == 0 && element == 64) return default;
            string name = kind switch { 0 or 1 => "dup", 5 when element < 32 => "umov", _ => "mov" };
            return new(Form.SimdCopy, name, kind switch { 2 => element, 5 => 32 << q, _ => width }, d, n,
                A: imm4 >> low, Mode: kind, Shift: index, Size: element);
        }
        if (Is(0xbfe08400, 0x2e000000) && Field(11, 4) < width / 8)
            return new(Form.SimdPermute, "ext", width, d, n, m, Shift: Field(11, 4), Size: 8);
        opName = (word & 0xbf20fc00) switch { 0x0e001800 => "uzp1", 0x0e005800 => "uzp2", 0x0e003800 => "zip1", _ => null };
        if (opName != null && width > size) return new(Form.SimdPermute, opName, width, d, n, m, Size: size);
        if (Is(0xbf3ffc00, 0x0e212800) && size < 64 || Is(0xbffffc00, 0x0e616800))
            return new(Form.SimdNarrow, (Field(14, 1) == 0 ? "xtn" : "fcvtn") + (q == 1 ? "2" : ""),
                width, d, n, Mode: q, Size: Field(14, 1) == 0 ? size : 32);
        if (Is(0xbffffc00, 0x0e617800))
            return new(Form.SimdWiden, q == 1 ? "fcvtl2" : "fcvtl", 128, d, n, Mode: q, Size: 32);
        if (Is(0xbf3ffc00, 0x0e31b800) || Is(0xbf3ffc00, 0x2e303800))
        {
            if (size == 64 || size == 32 && q == 0) return default;
            return new(Form.SimdReduce, Field(29, 1) == 0 ? "addv" : "uaddlv", width, d, n, Size: size);
        }
        if (Is(0xffbffc00, 0x7e30d800)) return new(Form.SimdReduce, "faddp", fp * 2, d, n, Size: fp);
        opName = (word & 0xbf80fc00) switch
        {
            0x2f00a400 => "ushll", 0x0f00a400 => "sshll", 0x0f005400 => "shl",
            0x0f000400 => "sshr", 0x2f000400 => "ushr", _ => null
        };
        int immediate = Field(16, 7);
        if (opName != null && immediate >= 8)
        {
            int element = 1 << BitOperations.Log2((uint)immediate);
            bool widen = opName.EndsWith("ll");
            if (element == 64 && (q == 0 || widen)) return default;
            return new(widen ? Form.SimdWiden : Form.SimdShift, opName + (widen && q == 1 ? "2" : ""), widen ? 128 : width,
                d, n, Mode: widen ? q : 0, Shift: opName.EndsWith("hr") ? element * 2 - immediate : immediate - element, Size: element);
        }
        if (Is(0x9ff80c00, 0x0f000400))
        {
            int cmode = Field(12, 4), u = Field(29, 1), literal = Field(16, 3) << 5 | Field(5, 5);
            if (cmode == 15 && (u == 0 || q == 1))
            {
                double number = Math.ScaleB(1.0 + (literal & 15) / 16.0, (((literal >> 4) & 7) ^ 4) - 3) * (literal < 128 ? 1 : -1);
                return new(Form.SimdFloatImmediate, "fmov", width, d, Imm: u == 0 ? BitConverter.SingleToInt32Bits((float)number) : BitConverter.DoubleToInt64Bits(number), Size: 32 << u);
            }
            if (cmode is 12 or 13) return new(Form.SimdImmediate, u == 0 ? "movi" : "mvni", width, d, Imm: literal, Mode: 1, Shift: (cmode - 11) * 8, Size: 32);
            if (cmode < 12 && (cmode & 1) != 0)
                return new(Form.SimdImmediate, u == 0 ? "orr" : "bic", width, d, Imm: literal, Shift: (cmode < 8 ? cmode / 2 : (cmode - 8) / 2) * 8, Size: cmode < 8 ? 32 : 16);
        }
        if (Is(0xbf200000, 0x0d000000) && Field(13, 1) == 0)
        {
            bool load = Field(22, 1) == 1, post = Field(23, 1) == 1;
            int scale = Field(14, 2), s = Field(12, 1), sz = Field(10, 2);
            if (!post && m != 0 || scale == 3 && (!load || s != 0) || scale == 1 && (sz & 1) != 0 ||
                scale == 2 && (sz > 1 || sz == 1 && s != 0)) return default;
            int element = scale switch { 3 => 8 << sz, 2 => 32 << sz, _ => 8 << scale };
            int lane = (q * 8 + s * 4 + sz) / (element / 8);
            return new(Form.SimdTransfer, scale == 3 ? "ld1r" : load ? "ld1" : "st1", width, d, n, m, Mode: post ? 1 : 0, Shift: lane, Size: element);
        }
        if (Is(0xbffff000, 0x0c008000) && width > (8 << Field(10, 2)))
            return new(Form.SimdTransfer, "st2", width, d, n, Size: 8 << Field(10, 2));
        return default;
    }
}
