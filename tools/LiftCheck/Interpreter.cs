using System.Numerics;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

internal readonly record struct Bits(UInt128 Value, UInt128 Undefined = default)
{
    public static UInt128 Mask(int width) => UInt128.MaxValue >> (128 - width);
    public static Int128 Signed(UInt128 x, int w) => (Int128)(x << (128 - w)) >> (128 - w);
}

internal sealed class Interpreter(Image image, ulong seed, HashSet<EdgeId> covered)
{
    readonly Dictionary<ulong, byte> writes = [];
    readonly Trace trace = new();
    Bits[] values = [];
    int[] generations = [];
    int generation;
    Bits Store(Term term, Bits value)
    {
        generations[term.Id] = generation;
        return values[term.Id] = value;
    }
    // 在三值位上逐位做全加器。进位是否确定由三个输入中的多数位决定。
    static Bits Add(Bits a, Bits b, int width, bool subtract)
    {
        UInt128 mask = Bits.Mask(width);
        UInt128 right = subtract ? ~b.Value & mask : b.Value;
        UInt128 value = (subtract ? a.Value - b.Value : a.Value + b.Value) & mask;
        UInt128 unknown = 0;
        bool minCarry = subtract, maxCarry = subtract;
        for (int i = 0; i < width; i++)
        {
            UInt128 bit = UInt128.One << i;
            if (((a.Undefined | b.Undefined) & bit) != 0 || minCarry != maxCarry) unknown |= bit;
            bool minA = (a.Value & ~a.Undefined & bit) != 0, maxA = ((a.Value | a.Undefined) & bit) != 0;
            bool minB = (right & ~b.Undefined & bit) != 0, maxB = ((right | b.Undefined) & bit) != 0;
            minCarry = minA && minB || (minA || minB) && minCarry;
            maxCarry = maxA && maxB || (maxA || maxB) && maxCarry;
        }
        return new(value, unknown);
    }

    int calls;
    Bits Eval(Term t)
    {
        if (generations[t.Id] == generation) return values[t.Id];
        Bits v;
        var mask = Bits.Mask(t.Width);
        Bits Child(int j) => Eval(t.Operands[j]);
        Bits a, b;
        switch (t.Kind)
        {
            case TermKind.Constant: v = new(t.Value); break;
            case TermKind.Undefined: v = new(0, mask); break;
            case TermKind.EntryParameter: v = new(EnvironmentState.Register(seed, Abi.Register(t.Slot)) & mask); break;
            case TermKind.Slice: a = Child(0); v = new((a.Value >> t.Offset) & mask, (a.Undefined >> t.Offset) & mask); break;
            case TermKind.Concat:
                int offset = 0; UInt128 bits = 0, bad = 0;
                foreach (var part in t.Operands)
                { a = Eval(part); bits |= a.Value << offset; bad |= a.Undefined << offset; offset += part.Width; }
                v = new(bits, bad); break;
            case TermKind.Select:
                a = Child(0);
                if (a.Undefined != 0)
                {
                    b = Child(1); var c = Child(2); v = new(b.Value, (b.Value ^ c.Value) | b.Undefined | c.Undefined);
                }
                else v = Child(a.Value == 0 ? 2 : 1);
                break;
            case TermKind.Operation:
                a = Child(0); b = t.Operands.Length > 1 ? Child(1) : default;
                if (t.Op == Op.And) v = new(a.Value & b.Value, (a.Undefined & (b.Value | b.Undefined)) | (b.Undefined & (a.Value | a.Undefined)));
                else if (t.Op == Op.Or) v = new(a.Value | b.Value, (a.Undefined & (~b.Value | b.Undefined)) | (b.Undefined & (~a.Value | a.Undefined)));
                else if (t.Op == Op.Xor) v = new(a.Value ^ b.Value, a.Undefined | b.Undefined);
                else if (t.Op == Op.Not) v = new(~a.Value & mask, a.Undefined);
                else if (a.Undefined != 0 && (t.Op is Op.SignExtend or Op.BitReverse or Op.ByteSwap ||
                    t.Op is Op.Shl or Op.LShr or Op.AShr && b.Undefined == 0))
                    v = new(Operation(t, a.Value, b.Value) & mask, Operation(t, a.Undefined, b.Value) & mask);
                else if (t.Op is Op.FNeg or Op.FAbs)
                    v = new(Operation(t, a.Value, 0), a.Undefined & (t.Op == Op.FAbs ? mask >> 1 : mask));
                else if ((a.Undefined | b.Undefined) != 0 && t.Op is Op.Add or Op.Sub or Op.Neg)
                    v = t.Op == Op.Neg ? Add(default, a, t.Width, true) : Add(a, b, t.Width, t.Op == Op.Sub);
                else if (t.Op == Op.Eq && ((a.Value ^ b.Value) & ~(a.Undefined | b.Undefined)) != 0) v = new(0);
                else if ((a.Undefined | b.Undefined) != 0 || t.Operands.Length == 3 && Child(2).Undefined != 0) v = new(0, mask);
                else v = new(Operation(t, a.Value, b.Value) & mask);
                break;
            default: throw new InvalidDataException($"项无值 {t.Kind}");
        }
        return Store(t, v);
    }

    UInt128 Operation(Term t, UInt128 a, UInt128 b)
    {
        int width = t.Operands[0].Width;
        Int128 x = Bits.Signed(a, width), y = Bits.Signed(b, width);
        UInt128 mask = Bits.Mask(width);
        UInt128 Bit(bool condition) => condition ? UInt128.One : UInt128.Zero;
        switch (t.Op)
        {
            case Op.Add: return a + b;
            case Op.Sub: return a - b;
            case Op.Mul: return a * b;
            case Op.Neg: return 0 - a;
            case Op.UDiv: return b == 0 ? mask : a / b;
            case Op.URem: return b == 0 ? a : a % b;
            case Op.SDiv: return y == 0 ? mask : y == -1 ? 0 - a : (UInt128)(x / y);
            case Op.SRem: return y == 0 ? a : y == -1 ? 0 : (UInt128)(x % y);
            case Op.UMulHigh: return width <= 64 ? (a * b) >> width : UInt128.CreateTruncating(((BigInteger)a * b) >> width);
            case Op.SMulHigh: return width <= 64 ? (UInt128)((x * y) >> width) : UInt128.CreateTruncating(((BigInteger)x * y) >> width);
            case Op.Eq: return Bit(a == b);
            case Op.Ult: return Bit(a < b);
            case Op.Slt: return Bit(x < y);
            case Op.Shl: return b >= (uint)width ? 0 : a << (int)b;
            case Op.LShr: return b >= (uint)width ? 0 : a >> (int)b;
            case Op.AShr: return (UInt128)(x >> (int)UInt128.Min(b, (uint)(width - 1)));
            case Op.SignExtend: return (UInt128)x;
            case Op.AddCarry: return Bit(a > mask - b);
            case Op.AddOverflow: return Bit((x < 0) == (y < 0) && (x < 0) != (Bits.Signed(a + b, width) < 0));
            case Op.SubOverflow: return Bit((x < 0) != (y < 0) && (x < 0) != (Bits.Signed(a - b, width) < 0));
            case Op.CountLeadingZeros: return UInt128.LeadingZeroCount(a) - (uint)(128 - width);
            case Op.CountTrailingZeros: return UInt128.Min((uint)width, UInt128.TrailingZeroCount(a));
            case Op.PopCount: return UInt128.PopCount(a);
            case Op.BitReverse:
            case Op.ByteSwap:
                int unit = t.Op == Op.ByteSwap ? 8 : 1;
                UInt128 reversed = 0;
                for (int j = 0; j < width; j += unit) reversed = (reversed << unit) | ((a >> j) & Bits.Mask(unit));
                return reversed;
            case Op.SToF: return t.Width == 32 ? BitConverter.SingleToUInt32Bits((float)x) : BitConverter.DoubleToUInt64Bits((double)x);
            case Op.UToF: return t.Width == 32 ? BitConverter.SingleToUInt32Bits((float)a) : BitConverter.DoubleToUInt64Bits((double)a);
            case Op.FConvert:
                return t.Width == 32 ? BitConverter.SingleToUInt32Bits((float)BitConverter.UInt64BitsToDouble((ulong)a)) :
                    BitConverter.DoubleToUInt64Bits(BitConverter.UInt32BitsToSingle((uint)a));
            case Op.FToSIndefinite:
            case Op.FToSSaturate:
            case Op.FToUSaturate:
                double number = width == 32 ? BitConverter.UInt32BitsToSingle((uint)a) : BitConverter.UInt64BitsToDouble((ulong)a);
                if (t.Op == Op.FToSIndefinite)
                {
                    double bound = Math.ScaleB(1, t.Width - 1);
                    if (double.IsNaN(number) || Math.Truncate(number) < -bound || Math.Truncate(number) >= bound)
                        return UInt128.One << (t.Width - 1);
                }
                if (double.IsNaN(number)) return 0;
                if (t.Op == Op.FToUSaturate) return t.Width == 32 ? uint.CreateSaturating(number) : ulong.CreateSaturating(number);
                return (UInt128)(t.Width == 32 ? int.CreateSaturating(number) : long.CreateSaturating(number));
            case Op.FNeg: return a ^ (UInt128.One << (width - 1));
            case Op.FAbs: return a & (mask >> 1);
        }
        UInt128 c = t.Operands.Length == 3 ? Eval(t.Operands[2]).Value : 0;
        return width == 32 ? Float<float, uint>(t, (uint)a, (uint)b, (uint)c) : Float<double, ulong>(t, (ulong)a, (ulong)b, (ulong)c);
    }

    static UInt128 Float<F, U>(Term t, U a, U b, U c) where F : unmanaged, IFloatingPointIeee754<F> where U : unmanaged, IBinaryInteger<U>
    {
        F x = System.Runtime.CompilerServices.Unsafe.BitCast<U, F>(a), y = System.Runtime.CompilerServices.Unsafe.BitCast<U, F>(b);
        F z = System.Runtime.CompilerServices.Unsafe.BitCast<U, F>(c);
        if (t.Op is Op.FLt or Op.FEq or Op.FLe or Op.FUnordered)
        {
            bool condition = t.Op switch { Op.FLt => x < y, Op.FEq => x == y, Op.FLe => x <= y, _ => F.IsNaN(x) || F.IsNaN(y) };
            return condition ? UInt128.One : UInt128.Zero;
        }
        if (F.IsNaN(x) || F.IsNaN(y) || F.IsNaN(z))
        {
            // FPCR 默认模式的 FPProcessNaNs：信令 NaN 优先，同类按操作数顺序，保留符号与负载。
            UInt128 quiet = t.Operands[0].Width == 32 ? 1u << 22 : 1ul << 51;
            UInt128 ax = UInt128.CreateTruncating(a), by = UInt128.CreateTruncating(b), cz = UInt128.CreateTruncating(c);
            if (F.IsNaN(x) && (ax & quiet) == 0) return ax | quiet;
            if (F.IsNaN(y) && (by & quiet) == 0) return by | quiet;
            if (F.IsNaN(z) && (cz & quiet) == 0) return cz | quiet;
            if (t.Op == Op.Opaque)
            {
                var op = (ArmOperation)t.OpaqueCode;
                if (op is ArmOperation.MaximumNumber or ArmOperation.MinimumNumber && F.IsNaN(x) != F.IsNaN(y))
                    return F.IsNaN(x) ? by : ax;
                if (op == ArmOperation.FusedMultiplyAdd && F.IsNaN(x) &&
                    (F.IsZero(y) && F.IsInfinity(z) || F.IsInfinity(y) && F.IsZero(z)))
                    return t.Width == 32 ? 0x7fc00000u : 0x7ff8000000000000ul;
            }
            return F.IsNaN(x) ? ax : F.IsNaN(y) ? by : cz;
        }
        F result = t.Op switch
        {
            Op.FAdd => x + y,
            Op.FSub => x - y,
            Op.FMul => x * y,
            Op.FDiv => x / y,
            Op.FRem => x % y,
            Op.FSqrt => F.Sqrt(x),
            Op.Opaque => (ArmOperation)t.OpaqueCode switch
            {
                ArmOperation.FusedMultiplyAdd => F.FusedMultiplyAdd(y, z, x),
                ArmOperation.Maximum => F.Max(x, y),
                ArmOperation.Minimum => F.Min(x, y),
                ArmOperation.MaximumNumber => F.MaxNumber(x, y),
                ArmOperation.MinimumNumber => F.MinNumber(x, y),
                ArmOperation.RoundEven => F.Round(x),
                ArmOperation.RoundPositive => F.Ceiling(x),
                ArmOperation.RoundNegative => F.Floor(x),
                ArmOperation.RoundZero => F.Truncate(x),
                _ => throw new InvalidDataException("未知目标运算")
            },
            _ => throw new InvalidDataException($"未知运算 {t.Op}")
        };
        // FPCR 默认设置下，由有效非 NaN 操作数产生的无效操作给出正的默认安静 NaN。
        if (F.IsNaN(result) && !F.IsNaN(x) && !F.IsNaN(y) && !F.IsNaN(z))
            return sizeof(float) == System.Runtime.CompilerServices.Unsafe.SizeOf<F>() ? 0x7fc00000u : 0x7ff8000000000000ul;
        return UInt128.CreateTruncating(System.Runtime.CompilerServices.Unsafe.BitCast<F, U>(result));
    }

    internal Bits Result(Term value) => Eval(value);

    UInt128 Observe(Term t, string role, ulong pc)
    {
        var v = Eval(t);
        if (v.Undefined != 0 && trace.Error == null)
        {
            trace.Error = "依赖未定义";
            trace.Diagnostic = $"{role}@{pc:x} 位掩码 {v.Undefined:x}";
        }
        return v.Value;
    }

    public Trace Run(MethodSnapshot snapshot, LiftLocations locations)
    {
        values = new Bits[snapshot.Terms.Count];
        generations = new int[values.Length];
        BlockId id = snapshot.Entry;
        Bits[] args = [];
        while (trace.Error == null)
        {
            var block = snapshot.Flow[id];
            int cost = locations.Blocks.GetValueOrDefault(id).Instructions;
            if (trace.Instructions + cost > EnvironmentState.StepLimit) { trace.Exhausted = true; break; }
            trace.Instructions += cost;
            generation++;
            for (int j = 0; j < args.Length; j++) Store(block.Parameters[j], args[j]);
            for (int j = 0; j < block.Occurrences.Length; j++)
            {
                var occurrence = block.Occurrences[j]; var results = block.Results[j];
                trace.Pc = occurrence.Address;
                switch (occurrence)
                {
                    case ReadOccurrence read:
                        ulong address = (ulong)Observe(read.Location, "读地址", read.Address); UInt128 value = 0;
                        if (trace.Error != null) return trace;
                        for (int k = 0; k < read.Width / 8; k++)
                        {
                            ulong at = address + (uint)k;
                            value |= (UInt128)(writes.TryGetValue(at, out var v) ? v : image.Byte(at, seed)) << (k * 8);
                        }
                        trace.Add("读", address, read.Width); Store(results[0], new(value)); break;
                    case WriteOccurrence write:
                        address = (ulong)Observe(write.Location, "写地址", write.Address); value = Observe(write.Value, "写值", write.Address);
                        if (trace.Error != null) return trace;
                        trace.Add("写", address, write.Value.Width, value);
                        for (int k = 0; k < write.Value.Width / 8; k++) writes[address + (uint)k] = (byte)(value >> (k * 8));
                        break;
                    case CallOccurrence call:
                        var target = (ulong)Observe(call.Target!, "调用目标", call.Address);
                        if (trace.Error != null) return trace;
                        trace.Add("调用", target);
                        for (int k = 0; k < call.Arguments.Length; k++)
                            trace.Row("实参", call.Arguments[k].Width, Eval(call.Arguments[k]), Abi.Register(call.ArgumentSlots[k]));
                        calls++;
                        for (int k = 0; k < results.Length; k++)
                            Store(results[k], new(EnvironmentState.Register(seed, Abi.Register(call.ResultSlots[k]), calls)));
                        break;
                    default: throw new InvalidDataException("未知出现");
                }
                if (trace.Error != null) return trace;
            }
            var end = block.Terminator; int edge = 0;
            trace.Pc = end.Address;
            if (end.Condition is { } condition)
            {
                var v = Observe(condition, "分支条件", end.Address);
                edge = end.Kind == TerminatorKind.Branch ? (v == 0 ? 1 : 0) : (int)UInt128.Min(v, (uint)(end.Exits.Length - 1));
                if (trace.Error != null) return trace;
            }
            var exit = end.Exits[edge]; covered.Add(new(id, edge));
            if (exit.Kind == ExitKind.Target)
            {
                // 本块参数已存入求值表，同宽的下一行可以复用数组。
                if (args.Length != exit.Arguments.Length) args = new Bits[exit.Arguments.Length];
                for (int j = 0; j < args.Length; j++) args[j] = Eval(exit.Arguments[j]);
                id = exit.Target;
                continue;
            }
            trace.Add(exit.Kind.ToString());
            if (exit.Kind == ExitKind.Return)
                for (int k = 0; k < exit.Arguments.Length; k++)
                    trace.Row("返回槽", exit.Arguments[k].Width, Eval(exit.Arguments[k]), Abi.Register(snapshot.ReturnSlots[k]));
            return trace;
        }
        return trace;
    }
}
