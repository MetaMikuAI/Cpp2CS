using System.Collections.Immutable;

namespace Cpp2CS.Snapshot;

/// <summary>
/// 项的构造与驻留。每个方法的恢复使用自己的池；池不是线程安全的。
///
/// 规范化只使用与使用位置无关的语义恒等式，分三组：
/// 位搬运（移位、掩码、扩展、截断、不相交位的合并）化成切片与拼接；
/// 只取 0 和 1 的值的各种写法归一；
/// 比较的方向与严格性、常量的结合归一。
/// 要求“两个操作数是同一个项”的恒等式，只在该项不含未定义的位时使用。
/// 操作数只接受本池构造的项：同一个池里结构相同的项是同一个实例，引用相等就是结构相等。
/// </summary>
public sealed class TermPool
{
    private sealed class Structure : IEqualityComparer<Term>
    {
        public bool Equals(Term? x, Term? y) => ReferenceEquals(x, y) || (x is not null && y is not null && x.SameStructure(y));
        public int GetHashCode(Term t) => unchecked((int)(t.StructuralHash ^ (t.StructuralHash >> 32)));
    }

    private readonly Dictionary<Term, Term> table = new(new Structure());

    /// <summary>已驻留的项数。</summary>
    public int Count => table.Count;

    private Term Intern(Term candidate)
    {
        if (table.TryGetValue(candidate, out var existing)) return existing;
        candidate.Id = table.Count;
        table.Add(candidate, candidate);
        return candidate;
    }

    private Term Make(TermKind kind, int width, ImmutableArray<Term> operands, Op op = Op.None, UInt128 payload = default,
        int a = 0, int b = 0, int c = 0, int d = 0)
    {
        foreach (var operand in operands) Own(operand);
        return Intern(new Term(this, kind, width, operands, op, payload, a, b, c, d));
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new ArgumentException(message);
    }

    /// <summary>项是否由本池构造。</summary>
    public bool Owns(Term term) => ReferenceEquals(term.Pool, this);

    private void Own(Term term)
    {
        if (!ReferenceEquals(term.Pool, this)) throw new ArgumentException($"项 {term} 来自别的项池");
    }

    private void Own(Term x, Term y) { Own(x); Own(y); }

    private void Own(ReadOnlySpan<Term> terms)
    {
        foreach (var term in terms) Own(term);
    }

    private static UInt128 Mask(int width) => width >= 128 ? UInt128.MaxValue : (UInt128.One << width) - 1;
    private static Int128 Signed(UInt128 value, int width) =>
        width >= 128 ? (Int128)value : (Int128)(value << (128 - width)) >> (128 - width);

    // ---- 原子 ----

    /// <summary>位型给定的常量，位宽不超过 128；高于位宽的位被丢弃。</summary>
    public Term Bits(UInt128 value, int width) => Constant(value, width);

    internal Term Constant(UInt128 value, int width)
    {
        Require(width is > 0 and <= 128, $"常量的位宽须在 1 到 128 之间：{width}");
        return Make(TermKind.Constant, width, [], payload: value & Mask(width));
    }

    /// <summary>整数常量：按补码截到给定的位宽。</summary>
    public Term Constant(long value, int width) => Constant(unchecked((UInt128)(Int128)value), width);
    public Term Zero(int width) => Constant(UInt128.Zero, width);
    public Term True => Constant(UInt128.One, 1);
    public Term False => Constant(UInt128.Zero, 1);

    public Term Undefined(int width)
    {
        Require(width > 0, "位宽须为正");
        return Make(TermKind.Undefined, width, []);
    }

    /// <summary>
    /// 任意值：在给定位置取定的未定义位（设计 7.2）。row 不小于 0 是出现的序号，−1 是终结的条件，−2−e 是第 e 个出口；
    /// 模板一侧的 row 是产生它的指令的偏移。由内核与模板的展开使用，前端不构造。
    /// </summary>
    public Term Arbitrary(int graph, BlockId block, int row, int index, long leaf, int width)
    {
        Require(width > 0 && block.Index >= 0 && leaf >= 0, "任意值的位宽、位置无效");
        return Make(TermKind.Arbitrary, width, [], payload: (ulong)leaf, a: graph, b: block.Index, c: row, d: index);
    }

    public Term EntryParameter(int graph, Slot slot, int width)
    {
        Require(width > 0, "位宽须为正");
        return Make(TermKind.EntryParameter, width, [], a: graph, b: (int)slot.Kind, c: slot.Index);
    }

    public Term BlockParameter(int graph, BlockId block, int index, int width)
    {
        Require(width > 0 && index >= 0 && block.Index >= 0, "块参数的位宽、序号无效");
        return Make(TermKind.BlockParameter, width, [], a: graph, b: block.Index, c: index);
    }

    public Term Result(int graph, OccurrenceId occurrence, int result, int width)
    {
        Require(width > 0 && result >= 0 && occurrence.Index >= 0, "结果的位宽、序号无效");
        return Make(TermKind.Result, width, [], a: graph, b: occurrence.Block.Index, c: occurrence.Index, d: result);
    }

    public Term Entity(EntityRef entity, int width)
    {
        Require(width > 0, "位宽须为正");
        return Make(TermKind.Entity, width, [], payload: unchecked((ulong)entity.Key), a: (int)entity.Kind);
    }

    public Term Attribute(AttributeId attribute, int width, params ReadOnlySpan<Term> operands)
    {
        Own(operands);
        Require(width > 0, "位宽须为正");
        return Make(TermKind.Attribute, width, [.. operands], a: attribute.Value);
    }

    // ---- 切片与拼接 ----

    public Term Slice(Term x, int offset, int width)
    {
        Own(x);
        // 先比宽度再比起点，避免 offset + width 在 32 位里溢出。
        Require(offset >= 0 && width > 0 && width <= x.Width && offset <= x.Width - width, $"切片 [{offset}+:{width}] 超出位宽 {x.Width}");
        if (offset == 0 && width == x.Width) return x;
        switch (x.Kind)
        {
            case TermKind.Constant:
                return Constant(x.Payload >> offset, width);
            case TermKind.Undefined:
                return Undefined(width);
            case TermKind.Slice:
                return Slice(x.Operands[0], x.A + offset, width);
            case TermKind.Concat:
            {
                var parts = new List<Term>();
                int at = 0;
                foreach (var part in x.Operands)
                {
                    int low = Math.Max(offset, at), high = Math.Min(offset + width, at + part.Width);
                    if (low < high) parts.Add(Slice(part, low - at, high - low));
                    at += part.Width;
                }
                return Concat(parts);
            }
            case TermKind.Select:
                return Select(x.Operands[0], Slice(x.Operands[1], offset, width), Slice(x.Operands[2], offset, width));
            case TermKind.Operation:
                switch (x.Op)
                {
                    // 按位运算逐位进行，与切片可交换。
                    case Op.And: return And(Slice(x.Operands[0], offset, width), Slice(x.Operands[1], offset, width));
                    case Op.Or: return Or(Slice(x.Operands[0], offset, width), Slice(x.Operands[1], offset, width));
                    case Op.Xor: return Xor(Slice(x.Operands[0], offset, width), Slice(x.Operands[1], offset, width));
                    case Op.Not: return Not(Slice(x.Operands[0], offset, width));
                    // 加、减、乘、取负的低位只取决于操作数的低位。
                    case Op.Add when offset == 0: return Add(Slice(x.Operands[0], 0, width), Slice(x.Operands[1], 0, width));
                    case Op.Sub when offset == 0: return Sub(Slice(x.Operands[0], 0, width), Slice(x.Operands[1], 0, width));
                    case Op.Mul when offset == 0: return Mul(Slice(x.Operands[0], 0, width), Slice(x.Operands[1], 0, width));
                    case Op.Neg when offset == 0: return Neg(Slice(x.Operands[0], 0, width));
                    case Op.SignExtend:
                    {
                        var inner = x.Operands[0];
                        if (offset + width <= inner.Width) return Slice(inner, offset, width);
                        if (offset < inner.Width) return SignExtend(Slice(inner, offset, inner.Width - offset), width);
                        return SignExtend(Slice(inner, inner.Width - 1, 1), width);
                    }
                }
                break;
        }
        return Make(TermKind.Slice, width, [x], a: offset);
    }

    /// <summary>拼接，操作数从低位到高位。</summary>
    public Term Concat(params ReadOnlySpan<Term> parts)
    {
        var list = new List<Term>(parts.Length);
        foreach (var part in parts) list.Add(part);
        return Concat(list);
    }

    public Term Concat(IReadOnlyList<Term> parts)
    {
        Require(parts.Count > 0, "拼接至少要有一个操作数");
        foreach (var part in parts) Own(part);
        var merged = new List<Term>(parts.Count);
        void Push(Term part)
        {
            if (part.Kind == TermKind.Concat)
            {
                foreach (var inner in part.Operands) Push(inner);
                return;
            }
            if (merged.Count > 0)
            {
                var last = merged[^1];
                // 相邻的常量合并；超过 128 位时，低位一段补满 128 位，余下的另成一段。
                if (last.Kind == TermKind.Constant && part.Kind == TermKind.Constant && last.Width < 128)
                {
                    if (last.Width + part.Width <= 128)
                    {
                        merged[^1] = Constant(last.Payload | (part.Payload << last.Width), last.Width + part.Width);
                        return;
                    }
                    int take = 128 - last.Width;
                    merged[^1] = Constant(last.Payload | (part.Payload << last.Width), 128);
                    merged.Add(Constant(part.Payload >> take, part.Width - take));
                    return;
                }
                if (last.Kind == TermKind.Undefined && part.Kind == TermKind.Undefined)
                {
                    merged[^1] = Undefined(last.Width + part.Width);
                    return;
                }
                // 同一个项上相邻的两段切片合成一段。
                if (last.Kind == TermKind.Slice && part.Kind == TermKind.Slice && ReferenceEquals(last.Operands[0], part.Operands[0])
                    && !last.Operands[0].HasUndefined && last.A + last.Width == part.A)
                {
                    merged.RemoveAt(merged.Count - 1);
                    Push(Slice(last.Operands[0], last.A, last.Width + part.Width));
                    return;
                }
            }
            merged.Add(part);
        }
        foreach (var part in parts) Push(part);
        if (merged.Count == 1) return merged[0];
        int width = 0;
        foreach (var part in merged) width = checked(width + part.Width);
        return Make(TermKind.Concat, width, [.. merged]);
    }

    public Term ZeroExtend(Term x, int width)
    {
        Own(x);
        Require(width >= x.Width, "零扩展的目标位宽不能更小");
        return width == x.Width ? x : Concat(x, Zeros(width - x.Width));
    }

    public Term Truncate(Term x, int width) => Slice(x, 0, width);

    /// <summary>任意位宽的全零：超过 128 位时拼接而成。</summary>
    private Term Zeros(int width)
    {
        if (width <= 128) return Zero(width);
        var parts = new List<Term>();
        for (int left = width; left > 0; left -= 128) parts.Add(Zero(Math.Min(left, 128)));
        return Make(TermKind.Concat, width, [.. parts]);
    }

    public Term SignExtend(Term x, int width)
    {
        Own(x);
        Require(width >= x.Width, "符号扩展的目标位宽不能更小");
        if (width == x.Width) return x;
        if (x.Kind == TermKind.Constant && width <= 128) return Constant(unchecked((UInt128)Signed(x.Payload, x.Width)), width);
        if (x.Kind == TermKind.Operation && x.Op == Op.SignExtend) return SignExtend(x.Operands[0], width);
        // 最高位已知为 0 时，符号扩展就是零扩展。
        if (x.Kind == TermKind.Concat && x.Operands[^1] is { Kind: TermKind.Constant } top && (top.Payload >> (top.Width - 1)) == UInt128.Zero)
            return ZeroExtend(x, width);
        return Make(TermKind.Operation, width, [x], Op.SignExtend);
    }

    // ---- 选择 ----

    public Term Select(Term condition, Term whenTrue, Term whenFalse)
    {
        Own(condition); Own(whenTrue, whenFalse);
        Require(condition.Width == 1, "选择的条件须为 1 位");
        Require(whenTrue.Width == whenFalse.Width, "选择的两支位宽须相同");
        if (condition.Kind == TermKind.Constant) return condition.Payload != UInt128.Zero ? whenTrue : whenFalse;
        if (ReferenceEquals(whenTrue, whenFalse)) return whenTrue;
        if (condition.Kind == TermKind.Operation && condition.Op == Op.Not) return Select(condition.Operands[0], whenFalse, whenTrue);
        // 只取 0 和 1 的值：选择 1 与 0 就是条件本身的零扩展。
        if (whenTrue.Kind == TermKind.Constant && whenFalse.Kind == TermKind.Constant)
        {
            if (whenTrue.Payload == UInt128.One && whenFalse.Payload == UInt128.Zero) return ZeroExtend(condition, whenTrue.Width);
            if (whenTrue.Payload == UInt128.Zero && whenFalse.Payload == UInt128.One) return ZeroExtend(Not(condition), whenTrue.Width);
        }
        return Make(TermKind.Select, whenTrue.Width, [condition, whenTrue, whenFalse]);
    }

    // ---- 运算 ----

    /// <summary>不带规范化的运算：浮点、计数、高半乘积等。按运算符的定义检查操作数个数与位宽（见 <see cref="Op"/>），然后驻留。</summary>
    public Term Operation(Op op, int width, params ReadOnlySpan<Term> operands)
    {
        Own(operands);
        Require(width > 0, "位宽须为正");
        Require(op is not (Op.None or Op.Opaque or Op.Add or Op.Sub or Op.Mul or Op.Neg or Op.And or Op.Or or Op.Xor or Op.Not
            or Op.Shl or Op.LShr or Op.AShr or Op.SignExtend or Op.Eq or Op.Ult or Op.Slt or Op.UDiv or Op.SDiv or Op.URem or Op.SRem),
            $"{op} 有专门的构造方法");
        CheckShape(op, width, operands);
        return Make(TermKind.Operation, width, [.. operands], op);
    }

    /// <summary>运算的形状：操作数个数，二元运算的两个操作数同宽，结果位宽与操作数的关系。</summary>
    private static void CheckShape(Op op, int width, ReadOnlySpan<Term> operands)
    {
        (int count, int result) = op switch
        {
            // result：0 表示结果位宽不受操作数约束，-1 表示与操作数同宽，正数表示固定位宽。
            Op.AddCarry or Op.AddOverflow or Op.SubOverflow => (2, 1),
            Op.UMulHigh or Op.SMulHigh => (2, -1),
            Op.CountLeadingZeros or Op.CountTrailingZeros or Op.PopCount => (1, 0),
            Op.ByteSwap or Op.BitReverse => (1, -1),
            Op.FAdd or Op.FSub or Op.FMul or Op.FDiv or Op.FRem => (2, -1),
            Op.FNeg or Op.FAbs or Op.FSqrt => (1, -1),
            Op.FEq or Op.FLt or Op.FLe or Op.FUnordered => (2, 1),
            Op.FConvert or Op.SToF or Op.UToF or Op.FToSSaturate or Op.FToUSaturate or Op.FToSIndefinite => (1, 0),
            _ => throw new ArgumentException($"{op} 没有登记形状"),
        };
        Require(operands.Length == count, $"{op} 要 {count} 个操作数，给了 {operands.Length} 个");
        if (count == 2) Require(operands[0].Width == operands[1].Width, $"{op} 的两个操作数位宽须相同：{operands[0].Width} 与 {operands[1].Width}");
        if (result > 0) Require(width == result, $"{op} 的结果是 {result} 位，不是 {width} 位");
        if (result < 0) Require(width == operands[0].Width, $"{op} 的结果与操作数同宽：{operands[0].Width} 位，不是 {width} 位");
        if (op == Op.ByteSwap) Require(width % 8 == 0, $"字节逆序的位宽须是 8 的倍数：{width}");
    }

    public Term Opaque(int code, int width, params ReadOnlySpan<Term> operands)
    {
        Own(operands);
        Require(width > 0, "位宽须为正");
        return Make(TermKind.Operation, width, [.. operands], Op.Opaque, a: code);
    }

    private static bool Before(Term x, Term y) => Term.CompareStructure(x, y) < 0;

    /// <summary>可交换运算的操作数次序：常量在右，其余按结构上的全序（先比结构散列）。</summary>
    private Term Commutative(Op op, Term x, Term y)
    {
        if (x.Kind == TermKind.Constant || (y.Kind != TermKind.Constant && Before(y, x))) (x, y) = (y, x);
        return Make(TermKind.Operation, op is Op.Eq ? 1 : x.Width, [x, y], op);
    }

    private static void SameWidth(Term x, Term y) => Require(x.Width == y.Width, $"两个操作数位宽须相同：{x.Width} 与 {y.Width}");
    private static bool SameDefined(Term x, Term y) => ReferenceEquals(x, y) && !x.HasUndefined;

    /// <summary>拆成“非常量部分 + 常量”。</summary>
    private static (Term? Remainder, UInt128 Addend) SplitSum(Term x)
    {
        if (x.Kind == TermKind.Constant) return (null, x.Payload);
        if (x.Kind == TermKind.Operation && x.Op == Op.Add && x.Operands[1].Kind == TermKind.Constant) return (x.Operands[0], x.Operands[1].Payload);
        return (x, UInt128.Zero);
    }

    public Term Add(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Width > 128) return Commutative(Op.Add, x, y);
        if (DisjointBits(x, y) is { } joined) return joined;
        var (xr, xc) = SplitSum(x);
        var (yr, yc) = SplitSum(y);
        var constant = Constant(unchecked(xc + yc), x.Width);
        Term? rest = xr is null ? yr : yr is null ? xr : Commutative(Op.Add, xr, yr);
        if (rest is null) return constant;
        return constant.IsZero ? rest : Commutative(Op.Add, rest, constant);
    }

    public Term Sub(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (SameDefined(x, y)) return Zeros(x.Width);
        if (y.Kind == TermKind.Constant) return Add(x, Constant(unchecked(UInt128.Zero - y.Payload), y.Width));
        return Make(TermKind.Operation, x.Width, [x, y], Op.Sub);
    }

    public Term Mul(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Kind == TermKind.Constant) (x, y) = (y, x);
        if (y.Kind == TermKind.Constant)
        {
            if (x.Kind == TermKind.Constant) return Constant(unchecked(x.Payload * y.Payload), x.Width);
            if (y.Payload == UInt128.Zero) return y;
            if (y.Payload == UInt128.One) return x;
            if (UInt128.IsPow2(y.Payload)) return ShiftLeft(x, (int)UInt128.TrailingZeroCount(y.Payload));
        }
        return Commutative(Op.Mul, x, y);
    }

    public Term Neg(Term x)
    {
        Own(x);
        if (x.Kind == TermKind.Constant) return Constant(unchecked(UInt128.Zero - x.Payload), x.Width);
        if (x.Kind == TermKind.Operation && x.Op == Op.Neg) return x.Operands[0];
        return Make(TermKind.Operation, x.Width, [x], Op.Neg);
    }

    /// <summary>无符号或有符号的除与余。除数为常量 1 时化简；两个常量且除数非零时求值。</summary>
    public Term Divide(Op op, Term x, Term y)
    {
        Require(op is Op.UDiv or Op.SDiv or Op.URem or Op.SRem, "须为除或余");
        Own(x, y);
        SameWidth(x, y);
        if (y.Kind == TermKind.Constant && y.Payload != UInt128.Zero && x.Width <= 128)
        {
            if (y.Payload == UInt128.One) return op is Op.UDiv or Op.SDiv ? x : Zero(x.Width);
            if (x.Kind == TermKind.Constant)
            {
                Int128 sx = Signed(x.Payload, x.Width), sy = Signed(y.Payload, y.Width);
                bool overflow = sy == -1 && x.Payload == UInt128.One << (x.Width - 1);
                return op switch
                {
                    Op.UDiv => Constant(x.Payload / y.Payload, x.Width),
                    Op.URem => Constant(x.Payload % y.Payload, x.Width),
                    Op.SDiv => overflow ? x : Constant(unchecked((UInt128)(sx / sy)), x.Width),
                    _ => overflow ? Zero(x.Width) : Constant(unchecked((UInt128)(sx % sy)), x.Width),
                };
            }
        }
        return Make(TermKind.Operation, x.Width, [x, y], op);
    }

    /// <summary>
    /// 两个值在每一段上至多一个不是常量 0 时，或、异或、加都等于把各段拼起来。
    /// 这是寄存器对、位域插入、向量车道合并的统一写法。
    /// </summary>
    private Term? DisjointBits(Term x, Term y)
    {
        static bool HasZeroPart(Term t)
        {
            if (t.Kind != TermKind.Concat) return false;
            foreach (var part in t.Operands) if (part.IsZero) return true;
            return false;
        }
        if (!HasZeroPart(x) && !HasZeroPart(y)) return null;
        var cuts = new SortedSet<int> { 0, x.Width };
        void Cuts(Term t)
        {
            if (t.Kind != TermKind.Concat) return;
            int at = 0;
            foreach (var part in t.Operands) cuts.Add(at += part.Width);
        }
        Cuts(x); Cuts(y);
        var parts = new List<Term>();
        int low = 0;
        foreach (int high in cuts)
        {
            if (high == 0) continue;
            Term a = Slice(x, low, high - low), b = Slice(y, low, high - low);
            if (a.IsZero) parts.Add(b);
            else if (b.IsZero) parts.Add(a);
            else return null;
            low = high;
        }
        return Concat(parts);
    }

    public Term And(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Kind == TermKind.Constant) (x, y) = (y, x);
        if (SameDefined(x, y)) return x;
        if (y.Kind == TermKind.Constant)
        {
            if (x.Kind == TermKind.Constant) return Constant(x.Payload & y.Payload, x.Width);
            if (y.Payload == UInt128.Zero) return y;
            if (y.Payload == Mask(y.Width)) return x;
            // 掩码把值切成“保留的段”与“清零的段”。
            var parts = new List<Term>();
            int at = 0;
            while (at < y.Width)
            {
                bool keep = ((y.Payload >> at) & UInt128.One) != UInt128.Zero;
                int end = at;
                while (end < y.Width && (((y.Payload >> end) & UInt128.One) != UInt128.Zero) == keep) end++;
                parts.Add(keep ? Slice(x, at, end - at) : Zero(end - at));
                at = end;
            }
            if (parts.Count <= 8) return Concat(parts);
        }
        return Commutative(Op.And, x, y);
    }

    public Term Or(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Kind == TermKind.Constant) (x, y) = (y, x);
        if (SameDefined(x, y)) return x;
        if (y.Kind == TermKind.Constant)
        {
            if (x.Kind == TermKind.Constant) return Constant(x.Payload | y.Payload, x.Width);
            if (y.Payload == UInt128.Zero) return x;
            if (y.Payload == Mask(y.Width)) return y;
        }
        return DisjointBits(x, y) ?? Commutative(Op.Or, x, y);
    }

    public Term Xor(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Kind == TermKind.Constant) (x, y) = (y, x);
        if (SameDefined(x, y)) return Zeros(x.Width);
        if (y.Kind == TermKind.Constant)
        {
            if (x.Kind == TermKind.Constant) return Constant(x.Payload ^ y.Payload, x.Width);
            if (y.Payload == UInt128.Zero) return x;
            if (y.Payload == Mask(y.Width)) return Not(x);
        }
        return DisjointBits(x, y) ?? Commutative(Op.Xor, x, y);
    }

    public Term Not(Term x)
    {
        Own(x);
        if (x.Kind == TermKind.Constant) return Constant(~x.Payload, x.Width);
        if (x.Kind == TermKind.Operation && x.Op == Op.Not) return x.Operands[0];
        return Make(TermKind.Operation, x.Width, [x], Op.Not);
    }

    private Term ShiftLeft(Term x, int amount) =>
        amount == 0 ? x : amount >= x.Width ? Zeros(x.Width) : Concat(Zeros(amount), Slice(x, 0, x.Width - amount));

    private Term Shift(Op op, Term x, Term amount)
    {
        Own(x, amount);
        SameWidth(x, amount);
        if (amount.Kind != TermKind.Constant) return Make(TermKind.Operation, x.Width, [x, amount], op);
        int width = x.Width;
        int n = amount.Payload >= (UInt128)width ? width : (int)amount.Payload;
        if (n == 0) return x;
        switch (op)
        {
            case Op.Shl: return ShiftLeft(x, n);
            case Op.LShr: return n >= width ? Zeros(width) : Concat(Slice(x, n, width - n), Zeros(n));
            default: return SignExtend(n >= width ? Slice(x, width - 1, 1) : Slice(x, n, width - n), width);
        }
    }

    public Term Shl(Term x, Term amount) => Shift(Op.Shl, x, amount);
    public Term LShr(Term x, Term amount) => Shift(Op.LShr, x, amount);
    public Term AShr(Term x, Term amount) => Shift(Op.AShr, x, amount);

    // ---- 比较 ----

    public Term Eq(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (x.Kind == TermKind.Constant) (x, y) = (y, x);
        if (SameDefined(x, y)) return True;
        if (y.Kind == TermKind.Constant)
        {
            UInt128 k = y.Payload;
            int width = x.Width;
            switch (x.Kind)
            {
                case TermKind.Constant:
                    return x.Payload == k ? True : False;
                case TermKind.Concat:
                {
                    // 各段里只有一段不是常量：常量段先比，剩下的是对那一段的比较。
                    Term? free = null;
                    int freeAt = 0, at = 0;
                    bool single = true, agree = true;
                    foreach (var part in x.Operands)
                    {
                        if (part.Kind == TermKind.Constant) agree &= part.Payload == ((k >> at) & Mask(part.Width));
                        else if (free is null) { free = part; freeAt = at; }
                        else single = false;
                        at += part.Width;
                    }
                    if (!agree) return False;
                    if (single && free is not null && free.Width <= 128) return Eq(free, Constant(k >> freeAt, free.Width));
                    break;
                }
                case TermKind.Operation:
                    switch (x.Op)
                    {
                        case Op.SignExtend:
                        {
                            var inner = x.Operands[0];
                            // 常量是它低位的符号扩展时，比较原值；否则不可能相等。
                            var low = Constant(k, inner.Width);
                            UInt128 extended = unchecked((UInt128)Signed(low.Payload, inner.Width)) & Mask(width);
                            return extended == k ? Eq(inner, low) : False;
                        }
                        case Op.Add when x.Operands[1].Kind == TermKind.Constant:
                            return Eq(x.Operands[0], Constant(unchecked(k - x.Operands[1].Payload), width));
                        case Op.Sub when k == UInt128.Zero:
                            return Eq(x.Operands[0], x.Operands[1]);
                        case Op.Xor when k == UInt128.Zero:
                            return Eq(x.Operands[0], x.Operands[1]);
                        case Op.Not:
                            return Eq(x.Operands[0], Constant(~k, width));
                        case Op.Neg:
                            return Eq(x.Operands[0], Constant(unchecked(UInt128.Zero - k), width));
                    }
                    break;
            }
            // 只取 0 和 1 的值：与 1 比较是它自己，与 0 比较是它的取反。
            if (width == 1) return k == UInt128.One ? x : Not(x);
        }
        return Commutative(Op.Eq, x, y);
    }

    public Term Ne(Term x, Term y) => Not(Eq(x, y));

    /// <summary>无符号小于。常量归到右边：c &lt; x 写成 非(x &lt; c + 1)。</summary>
    public Term Ult(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (SameDefined(x, y)) return False;
        int width = x.Width;
        if (width <= 128)
        {
            UInt128 max = Mask(width);
            if (x.Kind == TermKind.Constant && y.Kind == TermKind.Constant) return x.Payload < y.Payload ? True : False;
            if (x.Kind == TermKind.Constant)
                return x.Payload == max ? False : Not(Ult(y, Constant(x.Payload + 1, width)));
            if (y.Kind == TermKind.Constant)
            {
                UInt128 k = y.Payload;
                if (k == UInt128.Zero) return False;
                if (k == UInt128.One) return Eq(x, Zero(width));
                // 小于 2 的幂就是高位全零。
                if (UInt128.IsPow2(k))
                {
                    int bits = (int)UInt128.TrailingZeroCount(k);
                    return Eq(Slice(x, bits, width - bits), Zero(width - bits));
                }
            }
        }
        // 两边是同样位宽的值的零扩展时，比较原值；与常量比较时，常量超出原值的范围则恒成立。
        if (ZeroExtended(x) is { } nx)
        {
            if (ZeroExtended(y) is { } ny && nx.Width == ny.Width) return Ult(nx, ny);
            if (y.Kind == TermKind.Constant && nx.Width <= 128)
                return y.Payload > Mask(nx.Width) ? True : Ult(nx, Constant(y.Payload, nx.Width));
        }
        return Make(TermKind.Operation, 1, [x, y], Op.Ult);
    }

    private static Term? ZeroExtended(Term x) =>
        x.Kind == TermKind.Concat && x.Operands.Length == 2 && x.Operands[1].IsZero ? x.Operands[0] : null;

    /// <summary>有符号小于。与 0 比较就是符号位。</summary>
    public Term Slt(Term x, Term y)
    {
        Own(x, y);
        SameWidth(x, y);
        if (SameDefined(x, y)) return False;
        int width = x.Width;
        if (width <= 128)
        {
            UInt128 smax = Mask(width) >> 1, smin = smax + 1;
            if (x.Kind == TermKind.Constant && y.Kind == TermKind.Constant)
                return Signed(x.Payload, width) < Signed(y.Payload, width) ? True : False;
            if (x.Kind == TermKind.Constant)
                return x.Payload == smax ? False : Not(Slt(y, Constant(x.Payload + 1, width)));
            if (y.Kind == TermKind.Constant)
            {
                if (y.Payload == UInt128.Zero) return Slice(x, width - 1, 1);
                if (y.Payload == smin) return False;
            }
        }
        if (x.Kind == TermKind.Operation && x.Op == Op.SignExtend && y.Kind == TermKind.Operation && y.Op == Op.SignExtend
            && x.Operands[0].Width == y.Operands[0].Width)
            return Slt(x.Operands[0], y.Operands[0]);
        return Make(TermKind.Operation, 1, [x, y], Op.Slt);
    }

    public Term Ule(Term x, Term y) => Not(Ult(y, x));
    public Term Ugt(Term x, Term y) => Ult(y, x);
    public Term Uge(Term x, Term y) => Not(Ult(x, y));
    public Term Sle(Term x, Term y) => Not(Slt(y, x));
    public Term Sgt(Term x, Term y) => Slt(y, x);
    public Term Sge(Term x, Term y) => Not(Slt(x, y));

    // ---- 重建 ----

    /// <summary>
    /// 用新的操作数重建一个项，经过同样的规范化。代入时使用：操作数换掉之后，
    /// 结果与“从一开始就用新操作数构造”是同一个项。
    /// </summary>
    public Term Rebuild(Term t, ReadOnlySpan<Term> operands)
    {
        Own(t); Own(operands);
        Require(operands.Length == t.Operands.Length, "操作数个数须相同");
        return Construct(t, operands);
    }

    /// <summary>
    /// 照另一个项池里的项的形状，用本池的操作数构造同样的项，经过同样的规范化。常量与实体没有操作数，照值构造；
    /// 带标记的叶子与未定义占位的含义取决于所在的图，须由调用方另行给出。
    /// </summary>
    public Term Transplant(Term shape, ReadOnlySpan<Term> operands)
    {
        Own(operands);
        Require(operands.Length == shape.Operands.Length, "操作数个数须相同");
        return shape.Kind switch
        {
            TermKind.Constant => Constant(shape.Value, shape.Width),
            TermKind.Entity => Entity(shape.Entity, shape.Width),
            _ when operands.Length == 0 => throw new ArgumentException($"叶子 {shape} 须由调用方给出"),
            _ => Construct(shape, operands),
        };
    }

    private Term Construct(Term t, ReadOnlySpan<Term> operands)
    {
        switch (t.Kind)
        {
            case TermKind.Slice: return Slice(operands[0], t.A, t.Width);
            case TermKind.Concat: return Concat(operands);
            case TermKind.Select: return Select(operands[0], operands[1], operands[2]);
            case TermKind.Attribute: return Attribute(t.Attribute, t.Width, operands);
            case TermKind.Operation:
                return t.Op switch
                {
                    Op.Add => Add(operands[0], operands[1]),
                    Op.Sub => Sub(operands[0], operands[1]),
                    Op.Mul => Mul(operands[0], operands[1]),
                    Op.Neg => Neg(operands[0]),
                    Op.And => And(operands[0], operands[1]),
                    Op.Or => Or(operands[0], operands[1]),
                    Op.Xor => Xor(operands[0], operands[1]),
                    Op.Not => Not(operands[0]),
                    Op.Shl => Shl(operands[0], operands[1]),
                    Op.LShr => LShr(operands[0], operands[1]),
                    Op.AShr => AShr(operands[0], operands[1]),
                    Op.SignExtend => SignExtend(operands[0], t.Width),
                    Op.Eq => Eq(operands[0], operands[1]),
                    Op.Ult => Ult(operands[0], operands[1]),
                    Op.Slt => Slt(operands[0], operands[1]),
                    Op.UDiv or Op.SDiv or Op.URem or Op.SRem => Divide(t.Op, operands[0], operands[1]),
                    Op.Opaque => Opaque(t.A, t.Width, operands),
                    _ => Operation(t.Op, t.Width, operands),
                };
            default:
                return t;
        }
    }
}
