namespace Cpp2CS.Ir;

/// <summary>
/// IR 的具体解释器。用于差分测试（提升器对照 Unicorn、化简前后对照），不参与恢复流程。
/// 未初始化的内存按地址哈希取值，便于在另一侧复现。
/// 遇到无法求值的构造时记录 Failure 并返回 0；调用方必须检查 Failure，Failure 非空时结果无效。
/// </summary>
public sealed class Evaluator
{
    public readonly Dictionary<Storage, UInt128> Registers = new();
    public readonly Dictionary<ulong, byte> Written = new();
    /// <summary>当前标志位 NZCV（bit3=N, bit2=Z, bit1=C, bit0=V）；为 null 表示不可求值。</summary>
    public int? Nzcv;
    public ulong? NextPc;
    public string? Failure;

    public static byte MemoryByte(ulong address)
    {
        var z = address + 0x9E3779B97F4A7C15UL;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
        return (byte)(z ^ (z >> 31));
    }

    private UInt128 Fail(string what)
    {
        Failure ??= "unevaluable " + what;
        return 0;
    }

    private byte ReadByte(ulong address) => Written.TryGetValue(address, out var value) ? value : MemoryByte(address);

    private UInt128 ReadMemory(ulong address, int width)
    {
        UInt128 value = 0;
        for (var i = width / 8 - 1; i >= 0; i--) value = (value << 8) | ReadByte(address + (ulong)i);
        return value;
    }

    public void Run(IReadOnlyList<Stmt> statements, ulong pc, ulong nextPc)
    {
        foreach (var statement in statements)
        {
            if (Failure is not null || NextPc is not null) return;
            Execute(statement, nextPc);
        }
        NextPc ??= Failure is null ? nextPc : null;
    }

    private void Execute(Stmt statement, ulong nextPc)
    {
        switch (statement)
        {
            case Assign assign when assign.Target.Bank == Bank.Flags:
                Nzcv = FlagsOf(assign.Value);
                break;
            case Assign assign:
                Registers[assign.Target] = Eval(assign.Value) & Mask(assign.Target.Width);
                break;
            case Store store:
            {
                var address = (ulong)Eval(store.Target);
                var value = Eval(store.Value);
                for (var i = 0; i < store.Value.Width / 8; i++)
                    Written[address + (ulong)i] = (byte)(value >> (i * 8));
                break;
            }
            case Branch branch:
                NextPc = Eval(branch.Condition) != 0 ? branch.Target : branch.Fallthrough;
                break;
            case Jump jump:
                NextPc = jump.Target;
                break;
            case Call call:
                // 与硬件对照：调用写 LR 并转移
                var target = (ulong)Eval(call.Target);
                Registers[Storage.Gpr(30)] = nextPc;
                NextPc = target;
                break;
            case IndirectJump indirect:
                NextPc = (ulong)Eval(indirect.Target);
                break;
            case Return:
                NextPc = (ulong)Get(Storage.Gpr(30));
                break;
            case Nop:
                break;
            case Trap trap:
                Failure = "trap " + trap.Kind;
                break;
            case Opaque opaque:
                Failure = "opaque " + opaque.Text;
                break;
            default:
                throw new NotSupportedException(statement.GetType().Name);
        }
    }

    public UInt128 Get(Storage storage) => Registers.TryGetValue(storage, out var value) ? value : 0;

    private static UInt128 Mask(int width) => width >= 128 ? UInt128.MaxValue : (UInt128.One << width) - 1;

    private static long Signed(UInt128 value, int width) => width >= 64 ? (long)(ulong)value : ((long)(ulong)value << (64 - width)) >> (64 - width);

    public UInt128 Eval(Expr expr)
    {
        var value = expr switch
        {
            Const c => (UInt128)c.Value,
            Read read when read.Storage.Bank == Bank.Flags => throw new InvalidOperationException("标志位只能经 TestFlags 读取"),
            Read read => Get(read.Storage),
            Load load => ReadMemory((ulong)Eval(load.Address), load.Width),
            Binary binary => Binary(binary),
            Unary unary => Unary(unary),
            Compare compare => Compare(compare.Cond, Eval(compare.Left), Eval(compare.Right), compare.Left.Width) ? 1u : 0u,
            Convert convert => Convert(convert),
            Select select => Eval(select.Condition) != 0 ? Eval(select.True) : Eval(select.False),
            Logical logical => logical.IsAnd
                ? (Eval(logical.Left) != 0 && Eval(logical.Right) != 0 ? 1u : 0u)
                : (Eval(logical.Left) != 0 || Eval(logical.Right) != 0 ? 1u : 0u),
            Not not => Eval(not.Operand) == 0 ? 1u : 0u,
            Extract extract => Eval(extract.Operand) >> extract.Low,
            Insert insert => (Eval(insert.Base) & ~(Mask(insert.Value.Width) << insert.Low)) | ((Eval(insert.Value) & Mask(insert.Value.Width)) << insert.Low),
            TestFlags test => FlagsOf(test.FlagsValue) is { } nzcv ? (Holds(test.Code, nzcv) ? 1u : 0u) : Fail("flags"),
            Intrinsic intrinsic => Intrinsic(intrinsic),
            _ => Fail(expr.GetType().Name),
        };
        return value & Mask(expr.Width);
    }

    private UInt128 Intrinsic(Intrinsic intrinsic)
    {
        var args = intrinsic.Arguments;
        switch (intrinsic.Name)
        {
            case "vdup.8" or "vdup.16" or "vdup.32" or "vdup.64":
            {
                var size = int.Parse(intrinsic.Name.AsSpan(5));
                var element = Eval(args[0]) & Mask(size);
                UInt128 result = 0;
                for (var i = 0; i < intrinsic.Width; i += size) result |= element << i;
                return result;
            }
            default:
                return Fail(intrinsic.Name);
        }
    }

    private int? FlagsOf(Expr expr)
    {
        switch (expr)
        {
            case Read { Storage.Bank: Bank.Flags }:
                return Nzcv;
            case Flags flags:
            {
                var width = flags.OperandWidth;
                var a = Eval(flags.Left) & Mask(width);
                if (flags.Kind == FlagKind.FloatCompare)
                {
                    var b = Eval(flags.Right!) & Mask(width);
                    var (x, y) = (ToDouble(a, width), ToDouble(b, width));
                    if (double.IsNaN(x) || double.IsNaN(y)) return 0b0011;
                    return x == y ? 0b0110 : x < y ? 0b1000 : 0b0010;
                }
                if (flags.Kind == FlagKind.Logic)
                {
                    var r = flags.Right is null ? a : a & Eval(flags.Right) & Mask(width);
                    return Nz(r, width);
                }
                var right = Eval(flags.Right!) & Mask(width);
                var sub = flags.Kind == FlagKind.Sub;
                var result = (sub ? a - right : a + right) & Mask(width);
                var carry = sub ? a >= right : result < a;
                var sa = Signed(a, width);
                var sb = Signed(right, width);
                var sr = Signed(result, width);
                var overflow = sub ? (sa < 0) != (sb < 0) && (sr < 0) != (sa < 0) : (sa < 0) == (sb < 0) && (sr < 0) != (sa < 0);
                return Nz(result, width) | (carry ? 2 : 0) | (overflow ? 1 : 0);
            }
            case ConditionalFlags conditional:
                return Eval(conditional.Condition) != 0 ? FlagsOf(conditional.Taken) : conditional.Nzcv;
            case Unknown:
                return null;
            default:
                Fail("flags " + expr.GetType().Name);
                return null;
        }
    }

    private static int Nz(UInt128 result, int width) => (((result >> (width - 1)) & 1) != 0 ? 8 : 0) | (result == 0 ? 4 : 0);

    public static bool Holds(FlagCondition code, int nzcv)
    {
        var n = (nzcv & 8) != 0;
        var z = (nzcv & 4) != 0;
        var c = (nzcv & 2) != 0;
        var v = (nzcv & 1) != 0;
        return code switch
        {
            FlagCondition.Eq => z,
            FlagCondition.Ne => !z,
            FlagCondition.Hs => c,
            FlagCondition.Lo => !c,
            FlagCondition.Mi => n,
            FlagCondition.Pl => !n,
            FlagCondition.Vs => v,
            FlagCondition.Vc => !v,
            FlagCondition.Hi => c && !z,
            FlagCondition.Ls => !c || z,
            FlagCondition.Ge => n == v,
            FlagCondition.Lt => n != v,
            FlagCondition.Gt => !z && n == v,
            FlagCondition.Le => z || n != v,
            FlagCondition.Al or FlagCondition.Nv => true,
            _ => throw new NotSupportedException(code.ToString()),
        };
    }

    private UInt128 Binary(Binary binary)
    {
        var width = binary.Width;
        var a = Eval(binary.Left);
        var b = Eval(binary.Right);
        switch (binary.Op)
        {
            case BinOp.Add: return a + b;
            case BinOp.Sub: return a - b;
            case BinOp.Mul: return a * b;
            case BinOp.And: return a & b;
            case BinOp.Or: return a | b;
            case BinOp.Xor: return a ^ b;
            case BinOp.Shl: return a << (int)(b % (uint)width);
            case BinOp.LShr: return (a & Mask(width)) >> (int)(b % (uint)width);
            case BinOp.AShr:
            {
                var count = (int)(b % (uint)width);
                if (width > 64) return Fail("ashr128");
                return (ulong)(Signed(a, width) >> count);
            }
            case BinOp.Ror:
            {
                var count = (int)(b % (uint)width);
                a &= Mask(width);
                return count == 0 ? a : (a >> count) | (a << (width - count));
            }
            case BinOp.UDiv: return b == 0 ? 0 : a / b;
            case BinOp.URem: return b == 0 ? 0 : a % b;
            case BinOp.SDiv or BinOp.SRem:
            {
                var x = Signed(a, width);
                var y = Signed(b, width);
                if (y == 0) return 0;
                if (y == -1) return binary.Op == BinOp.SDiv ? (ulong)unchecked(-x) : 0;
                return (ulong)(binary.Op == BinOp.SDiv ? x / y : x % y);
            }
            case BinOp.MulHighU: return ((UInt128)(ulong)a * (ulong)b) >> 64;
            case BinOp.MulHighS: return (UInt128)(ulong)(long)(((Int128)(long)(ulong)a * (long)(ulong)b) >> 64);
            default: return FloatBinary(binary.Op, a, b, width);
        }
    }

    private UInt128 FloatBinary(BinOp op, UInt128 a, UInt128 b, int width)
    {
        if (op is BinOp.FMin or BinOp.FMax or BinOp.FMinNumber or BinOp.FMaxNumber)
            return FloatExtremum(op, (ulong)a, (ulong)b, width);
        var x = ToDouble(a, width);
        var y = ToDouble(b, width);
        if (width == 32)
        {
            var (fx, fy) = ((float)x, (float)y);
            var r = op switch
            {
                BinOp.FAdd => fx + fy,
                BinOp.FSub => fx - fy,
                BinOp.FMul => fx * fy,
                BinOp.FDiv => fx / fy,
                _ => (float)Fail(op.ToString()),
            };
            if (float.IsNaN(r) && !double.IsNaN(x) && !double.IsNaN(y)) return DefaultNaN(32);
            return BitConverter.SingleToUInt32Bits(r);
        }
        if (width != 64) return Fail("float" + width);
        var result = op switch
        {
            BinOp.FAdd => x + y,
            BinOp.FSub => x - y,
            BinOp.FMul => x * y,
            BinOp.FDiv => x / y,
            _ => (double)Fail(op.ToString()),
        };
        if (double.IsNaN(result) && !double.IsNaN(x) && !double.IsNaN(y)) return DefaultNaN(64);
        return BitConverter.DoubleToUInt64Bits(result);
    }

    private UInt128 FloatExtremum(BinOp op, ulong a, ulong b, int width)
    {
        if (width is not (32 or 64)) return Fail("float" + width);
        var absolute = width == 32 ? 0x7fffffffUL : 0x7fffffffffffffffUL;
        var infinity = width == 32 ? 0x7f800000UL : 0x7ff0000000000000UL;
        var quiet = width == 32 ? 0x00400000UL : 0x0008000000000000UL;
        bool NaN(ulong bits) => (bits & absolute) > infinity;
        // 先处理 sNaN，再处理 qNaN，避免宿主浮点转换提前改变载荷。
        if (NaN(a) && (a & quiet) == 0) return a | quiet;
        if (NaN(b) && (b & quiet) == 0) return b | quiet;
        if (op is BinOp.FMinNumber or BinOp.FMaxNumber)
        {
            if (NaN(a) && !NaN(b)) return b;
            if (NaN(b) && !NaN(a)) return a;
        }
        if (NaN(a)) return a | quiet;
        if (NaN(b)) return b | quiet;
        var minimum = op is BinOp.FMin or BinOp.FMinNumber;
        var x = ToDouble(a, width);
        var y = ToDouble(b, width);
        if (x == y) return minimum ? a | b : a & b;
        return (minimum ? x < y : x > y) ? a : b;
    }

    private double ToDouble(UInt128 bits, int width) => width switch
    {
        32 => BitConverter.UInt32BitsToSingle((uint)bits),
        64 => BitConverter.UInt64BitsToDouble((ulong)bits),
        16 => (double)BitConverter.UInt16BitsToHalf((ushort)bits),
        _ => (double)Fail("float" + width),
    };

    private UInt128 FromDouble(double value, int width) => width switch
    {
        32 => BitConverter.SingleToUInt32Bits((float)value),
        64 => BitConverter.DoubleToUInt64Bits(value),
        16 => BitConverter.HalfToUInt16Bits((Half)value),
        _ => Fail("float" + width),
    };

    private UInt128 Unary(Unary unary)
    {
        var width = unary.Width;
        var a = Eval(unary.Operand) & Mask(width);
        switch (unary.Op)
        {
            case UnOp.Neg: return UInt128.Zero - a;
            case UnOp.Not: return ~a;
            case UnOp.Clz: return UInt128.LeadingZeroCount(a) - (UInt128)(128 - width);
            case UnOp.Cls:
            {
                var sign = (a >> (width - 1)) & 1;
                var count = 0;
                for (var i = width - 2; i >= 0 && ((a >> i) & 1) == sign; i--) count++;
                return (UInt128)count;
            }
            case UnOp.PopCount: return UInt128.PopCount(a);
            case UnOp.Rbit:
            {
                UInt128 r = 0;
                for (var i = 0; i < width; i++) r |= ((a >> i) & 1) << (width - 1 - i);
                return r;
            }
            case UnOp.Bswap: return SwapBytes(a, width, width);
            case UnOp.Bswap16: return SwapBytes(a, width, 16);
            case UnOp.Bswap32: return SwapBytes(a, width, 32);
            case UnOp.FNeg: return a ^ (UInt128.One << (width - 1));
            case UnOp.FAbs: return a & ~(UInt128.One << (width - 1));
        }
        var x = ToDouble(a, width);
        if (width == 32)
        {
            var f = (float)x;
            float r = unary.Op switch
            {
                UnOp.FSqrt => MathF.Sqrt(f),
                UnOp.FFloor => MathF.Floor(f),
                UnOp.FCeil => MathF.Ceiling(f),
                UnOp.FTrunc => MathF.Truncate(f),
                UnOp.FRoundEven or UnOp.FRoundCurrent => MathF.Round(f, MidpointRounding.ToEven),
                UnOp.FRoundAway => MathF.Round(f, MidpointRounding.AwayFromZero),
                _ => (float)Fail(unary.Op.ToString()),
            };
            if (float.IsNaN(r) && !float.IsNaN(f)) return DefaultNaN(32);
            return BitConverter.SingleToUInt32Bits(r);
        }
        var result = unary.Op switch
        {
            UnOp.FSqrt => Math.Sqrt(x),
            UnOp.FFloor => Math.Floor(x),
            UnOp.FCeil => Math.Ceiling(x),
            UnOp.FTrunc => Math.Truncate(x),
            UnOp.FRoundEven or UnOp.FRoundCurrent => Math.Round(x, MidpointRounding.ToEven),
            UnOp.FRoundAway => Math.Round(x, MidpointRounding.AwayFromZero),
            _ => (double)Fail(unary.Op.ToString()),
        };
        if (double.IsNaN(result) && !double.IsNaN(x)) return DefaultNaN(width);
        return FromDouble(result, width);
    }

    /// <summary>无效运算产生的默认 NaN（ARM 为正号静默 NaN；.NET 在 x64 上会给出负号）。</summary>
    private static UInt128 DefaultNaN(int width) => width switch
    {
        32 => 0x7FC00000u,
        16 => 0x7E00u,
        _ => 0x7FF8000000000000UL,
    };

    private static UInt128 SwapBytes(UInt128 value, int width, int unit)
    {
        UInt128 result = 0;
        for (var start = 0; start < width; start += unit)
            for (var i = 0; i < unit / 8; i++)
                result |= ((value >> (start + i * 8)) & 0xFF) << (start + unit - 8 - i * 8);
        return result;
    }

    private bool Compare(Cond cond, UInt128 a, UInt128 b, int width)
    {
        a &= Mask(width);
        b &= Mask(width);
        if (cond >= Cond.FEq && cond <= Cond.FUne)
        {
            var x = ToDouble(a, width);
            var y = ToDouble(b, width);
            var unordered = double.IsNaN(x) || double.IsNaN(y);
            return cond switch
            {
                Cond.FEq => x == y,
                Cond.FNe => !unordered && x != y,
                Cond.FLt => x < y,
                Cond.FLe => x <= y,
                Cond.FGt => x > y,
                Cond.FGe => x >= y,
                Cond.FUnordered => unordered,
                Cond.FOrdered => !unordered,
                Cond.FUlt => unordered || x < y,
                Cond.FUle => unordered || x <= y,
                Cond.FUgt => unordered || x > y,
                Cond.FUge => unordered || x >= y,
                Cond.FUeq => unordered || x == y,
                _ => unordered || x != y,
            };
        }
        var sa = Signed(a, Math.Min(width, 64));
        var sb = Signed(b, Math.Min(width, 64));
        return cond switch
        {
            Cond.Eq => a == b,
            Cond.Ne => a != b,
            Cond.Slt => sa < sb,
            Cond.Sle => sa <= sb,
            Cond.Sgt => sa > sb,
            Cond.Sge => sa >= sb,
            Cond.Ult => a < b,
            Cond.Ule => a <= b,
            Cond.Ugt => a > b,
            Cond.Uge => a >= b,
            Cond.Neg => sa < 0,
            Cond.NotNeg => sa >= 0,
            _ => Fail(cond.ToString()) != 0,
        };
    }

    private UInt128 Convert(Convert convert)
    {
        var from = convert.Operand.Width;
        var to = convert.Width;
        var a = Eval(convert.Operand) & Mask(from);
        switch (convert.Kind)
        {
            case ConvKind.ZeroExtend or ConvKind.Truncate or ConvKind.Bitcast: return a;
            case ConvKind.SignExtend: return (UInt128)(Int128)Signed(a, from);
            case ConvKind.SIntToFloat: return FromInteger((double)Signed(a, from), (float)Signed(a, from), to);
            case ConvKind.UIntToFloat: return FromInteger((double)(ulong)a, (float)(ulong)a, to);
            case ConvKind.FloatToFloat: return FromDouble(ToDouble(a, from), to);
            case ConvKind.FloatToSInt:
            {
                var x = ToDouble(a, from);
                if (double.IsNaN(x)) return 0;
                var min = -Math.Pow(2, to - 1);
                var max = Math.Pow(2, to - 1);
                if (x <= min) return (UInt128)(Int128)(long)min;
                if (x >= max) return (ulong)(long)(max - 1 >= long.MaxValue ? long.MaxValue : (long)max - 1);
                return (UInt128)(Int128)(long)Math.Truncate(x);
            }
            case ConvKind.FloatToUInt:
            {
                var x = ToDouble(a, from);
                if (double.IsNaN(x) || x <= 0) return 0;
                if (x >= Math.Pow(2, to)) return Mask(to);
                return (ulong)Math.Truncate(x);
            }
            default: return Fail(convert.Kind.ToString());
        }
    }

    // 整数到单精度要直接一次舍入，不能经过 double 二次舍入
    private UInt128 FromInteger(double asDouble, float asSingle, int width) => width switch
    {
        32 => BitConverter.SingleToUInt32Bits(asSingle),
        _ => FromDouble(asDouble, width),
    };
}

