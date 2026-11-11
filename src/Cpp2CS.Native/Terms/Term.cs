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
    internal Term(TermTable table, TermKind kind, int width, object? payload, ImmutableArray<Term> operands)
    {
        Table = table;
        Kind = kind;
        Width = width;
        Payload = payload;
        Operands = operands;
    }
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

public sealed class TermTable
{
    private readonly Dictionary<Key, Term> terms = new();
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
    public Term Apply(Operator op, int width, params Term[] operands)
    {
        ArgumentNullException.ThrowIfNull(op);
        Width(width);
        var values = Own(operands);
        if (!op.Accepts(width, values.Select(t => t.Width).ToImmutableArray()))
            throw new ArgumentException("运算的位宽或形状不合法。", nameof(operands));
        // 核心规范化规则只在这个入口接入；扩展运算保持不解释。
        return Intern(TermKind.Operation, width, op, values);
    }
    public Term Slice(Term source, int low, int width)
    {
        Width(width);
        var values = Own([source]);
        if (low < 0 || (long)low + width > source.Width) throw new ArgumentOutOfRangeException(nameof(low));
        return Intern(TermKind.Slice, width, low, values);
    }
    public Term Concat(params Term[] lowToHigh)
    {
        var values = Own(lowToHigh);
        if (values.Length == 0) throw new ArgumentException("拼接不能为空。", nameof(lowToHigh));
        return Intern(TermKind.Concat, checked(values.Sum(t => t.Width)), null, values);
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
        if (!terms.TryGetValue(key, out var term)) terms.Add(key, term = new(this, kind, width, payload, operands));
        return term;
    }
    private sealed record Key(TermKind Kind, int Width, object? Payload, ImmutableArray<Term> Operands)
    {
        public bool Equals(Key? other) => other is not null && Kind == other.Kind && Width == other.Width
            && Equals(Payload, other.Payload) && Operands.SequenceEqual(other.Operands);
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
