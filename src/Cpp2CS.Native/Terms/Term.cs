using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Native.Terms;

public enum TermKind { Constant, Undefined, Unknown, Operation, Slice, Concat, Atom }

/// <summary>扩展标识必须不可变，按值相等；StableText 描述值内容或原子种类，不含运行时哈希；含引用身份的原子由转储为引用身份编号。</summary>
public abstract record AtomIdentity
{
    public abstract string StableText { get; }
}

public sealed record Reason(string Code, string Message, Reason? Cause = null);

/// <summary>未知来源的身份；原因相同不意味着未知值相等。</summary>
public sealed class UnknownIdentity;
public sealed record UnknownValue(UnknownIdentity Identity, Reason Reason);

/// <summary>只能经所属项表构造；相等就是引用相等。</summary>
public sealed class Term
{
    internal Term(TermTable table, TermKind kind, int width, object? payload, ImmutableArray<Term> operands, int order)
    {
        Order = order;
        ContainsUndefined = kind == TermKind.Undefined;
        foreach (var operand in operands) ContainsUndefined |= operand.ContainsUndefined;
        Table = table;
        Kind = kind;
        Width = width;
        Payload = payload;
        Operands = operands;
    }
    internal int Order { get; }
    /// <summary>项的运算子图是否含未定义项；不判断运算的动态定义域。</summary>
    public bool ContainsUndefined { get; }
    public TermTable Table { get; }
    public TermKind Kind { get; }
    public int Width { get; }
    public object? Payload { get; }
    public ImmutableArray<Term> Operands { get; }
    public Operator? Operator => Payload as Operator;
    public BigInteger? ConstantValue => Kind == TermKind.Constant ? (BigInteger)Payload! : null;
    public int? SliceLow => Kind == TermKind.Slice ? (int)Payload! : null;
    public AtomIdentity? Identity => Payload as AtomIdentity;
    public Reason? Why => (Payload as UnknownValue)?.Reason;
}

public sealed partial class TermTable
{
    public TermTable() { }
    internal TermTable(bool normalize) => normalizationEnabled = normalize;
    private readonly bool normalizationEnabled = true;

    private readonly Dictionary<Key, Term> terms = new();
    private readonly Dictionary<Key, Term> concatenations = new();
    private readonly Dictionary<AtomIdentity, int> atomWidths = new();

    public Term Constant(BigInteger value, int width)
    {
        Width(width);
        if (value.Sign < 0 || value >= (BigInteger.One << width)) throw new ArgumentOutOfRangeException(nameof(value));
        return Intern(TermKind.Constant, width, value, []);
    }
    public Term Undefined(int width) => Intern(TermKind.Undefined, width, null, []);
    /// <summary>省略身份时创建独立未知来源；复用身份与原因则驻留为同一项。</summary>
    public Term Unknown(int width, Reason why, UnknownIdentity? identity = null)
    {
        ArgumentNullException.ThrowIfNull(why);
        for (var reason = why; reason is not null; reason = reason.Cause)
            if (string.IsNullOrWhiteSpace(reason.Code) || string.IsNullOrWhiteSpace(reason.Message))
                throw new ArgumentException("未知项必须给出原因代码和说明。", nameof(why));
        return Intern(TermKind.Unknown, width, new UnknownValue(identity ?? new(), why), []);
    }
    public Term Atom(AtomIdentity identity, int width)
    {
        ArgumentNullException.ThrowIfNull(identity);
        Width(width);
        if (atomWidths.TryGetValue(identity, out var existing) && existing != width)
            throw new ArgumentException("同一原子身份不能具有不同位宽。", nameof(width));
        atomWidths[identity] = width;
        return Intern(TermKind.Atom, width, identity, []);
    }
    // 核心运算至多三个操作数；为常见扩展留栈空间，大扩展转堆以限制栈用量。
    private const int StackOperandCapacity = 16;
    private readonly Dictionary<OperationRequest, Term> operations = new();
    private readonly record struct OperationRequest(Operator Operator, int Width, Term A, Term? B, Term? C);

    public Term Apply(Operator op, int width, params ReadOnlySpan<Term> operands)
    {
        ArgumentNullException.ThrowIfNull(op);
        Width(width);
        foreach (var operand in operands)
            if (operand is null || !ReferenceEquals(operand.Table, this))
                throw new ArgumentException("操作数必须来自本项表。", nameof(operands));
        // 常用的一至三个操作数请求命中时不分配数组，也不重复验证或规范化。
        var small = operands.Length is > 0 and <= 3;
        var request = small ? new OperationRequest(op, width, operands[0],
            operands.Length > 1 ? operands[1] : null, operands.Length > 2 ? operands[2] : null) : default;
        if (small && operations.TryGetValue(request, out var known)) return known;
        Span<int> widths = operands.Length <= StackOperandCapacity ? stackalloc int[operands.Length] : new int[operands.Length];
        for (var i = 0; i < operands.Length; i++) widths[i] = operands[i].Width;
        var accepts = op is CoreOperator coreShape
            ? coreShape.Accepts(width, widths)
            : op.Accepts(width, ImmutableArray.Create<int>(widths));
        if (!accepts)
            throw new ArgumentException("运算的位宽或形状不合法。", nameof(operands));
        var values = ImmutableArray.Create(operands);
        var result = normalizationEnabled && op is CoreOperator core
            ? NormalizeOperation(core, width, values)
            : Intern(TermKind.Operation, width, op, values);
        if (small) operations.Add(request, result);
        return result;
    }

    public Term Slice(Term source, int low, int width)
    {
        Width(width);
        if (source is null || !ReferenceEquals(source.Table, this))
            throw new ArgumentException("操作数必须来自本项表。", nameof(source));
        if (low < 0 || (long)low + width > source.Width) throw new ArgumentOutOfRangeException(nameof(low));
        return normalizationEnabled ? NormalizeSlice(source, low, width) : Intern(TermKind.Slice, width, low, [source]);
    }
    public Term Concat(params Term[] lowToHigh)
    {
        var values = Own(lowToHigh);
        if (values.Length == 0) throw new ArgumentException("拼接不能为空。", nameof(lowToHigh));
        var width = 0;
        foreach (var value in values) width = checked(width + value.Width);
        if (!normalizationEnabled) return Intern(TermKind.Concat, width, null, values);
        var request = new Key(TermKind.Concat, width, null, values);
        if (concatenations.TryGetValue(request, out var known)) return known;
        var result = NormalizeConcat(values);
        concatenations.Add(request, result);
        return result;
    }
    private ImmutableArray<Term> Own(IEnumerable<Term> values)
    {
        var result = values.ToImmutableArray();
        if (result.Any(t => t is null || !ReferenceEquals(t.Table, this)))
            throw new ArgumentException("操作数必须来自本项表。", nameof(values));
        return result;
    }
    private static void Width(int width)
    {
        if (width <= 0) throw new ArgumentOutOfRangeException(nameof(width));
    }
    private Term Intern(TermKind kind, int width, object? payload, ImmutableArray<Term> operands)
    {
        Width(width);
        var key = new Key(kind, width, payload, operands);
        if (!terms.TryGetValue(key, out var term)) terms.Add(key, term = new(this, kind, width, payload, operands, terms.Count));
        return term;
    }
    private readonly record struct Key(TermKind Kind, int Width, object? Payload, ImmutableArray<Term> Operands)
    {
        public bool Equals(Key other) => Kind == other.Kind && Width == other.Width
            && Equals(Payload, other.Payload) && Operands.AsSpan().SequenceEqual(other.Operands.AsSpan());
        public override int GetHashCode()
        {
            var hash = new HashCode();
            hash.Add(Kind);
            hash.Add(Width);
            hash.Add(Payload);
            foreach (var term in Operands) hash.Add(term);
            return hash.ToHashCode();
        }
    }
}
