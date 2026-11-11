using System.Collections.Immutable;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.Queries;

/// <summary>默认值也是带原因的失败；成功值与原因互斥。值必须不可变。</summary>
public readonly struct Outcome<T>
{
    private static readonly Reason Uninitialized = new("query.uninitialized", "查询未构造结果。");
    private readonly T? value;
    private readonly Reason? why;
    private readonly bool success;
    private Outcome(T? value, Reason? why, bool success) { this.value = value; this.why = why; this.success = success; }
    public bool IsSuccess => success;
    public Reason? Why => success ? null : why ?? Uninitialized;
    public T Value => success ? value! : throw new InvalidOperationException("失败没有值。");
    public static Outcome<T> Success(T value) => new(value, null, true);
    public static Outcome<T> Failure(Reason why) => new(default, why ?? throw new ArgumentNullException(nameof(why)), false);
    public Outcome<U> Propagate<U>(string description = "依赖查询失败。") => !success
        ? Outcome<U>.Failure(new("query.dependency", description, Why))
        : throw new InvalidOperationException("成功结果不能传播为失败。");
}

/// <summary>实例是查询身份。实例、键、结果须不可变；依赖只能经上下文取得。</summary>
public abstract class Query<TKey, TValue> : Query where TKey : notnull
{
    protected Query(long stepBudget = long.MaxValue) : base(stepBudget) { }
    public abstract Outcome<TValue> Compute(QueryContext context, TKey key);
}

public abstract class Query
{
    private protected Query(long stepBudget)
    {
        if (stepBudget < 0) throw new ArgumentOutOfRangeException(nameof(stepBudget));
        StepBudget = stepBudget;
    }
    public sealed override bool Equals(object? obj) => ReferenceEquals(this, obj);
    public sealed override int GetHashCode() => System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(this);
    public long StepBudget { get; }
}

public sealed record QueryAddress(Query Query, object Key);
public sealed record QueryStatistics(long Computations, long Hits, long Failures);
public sealed record QueryTrace(QueryAddress Address, ImmutableArray<QueryAddress> Dependencies, Reason? Why);

/// <summary>偏序、最小值与最小上界由作者保证；所有值不可变。</summary>
public interface ILattice<T>
{
    T Bottom { get; }
    T Join(T left, T right);
    bool LessOrEqual(T left, T right);
}

public abstract class FixedPointMember
{
    private protected FixedPointMember(Query query) => Query = query;
    public Query Query { get; }
    public static FixedPointMember Create<K, V>(Query<K, V> query, Func<K, ILattice<V>> lattice) where K : notnull
        => new Member<K, V>(query, lattice);
    internal sealed class Member<K, V>(Query<K, V> query, Func<K, ILattice<V>> lattice) : FixedPointMember(query) where K : notnull
    {
        internal ILattice<V> Lattice(K key) => lattice(key);
    }
}

public sealed class FixedPointGroup
{
    public FixedPointGroup(long stepLimit, params FixedPointMember[] members)
    {
        if (stepLimit < 0) throw new ArgumentOutOfRangeException(nameof(stepLimit));
        if (members.Length == 0 || members.Select(m => m.Query).Distinct(ReferenceEqualityComparer.Instance).Count() != members.Length)
            throw new ArgumentException("组的查询必须非空且唯一。", nameof(members));
        StepLimit = stepLimit;
        Members = members.ToImmutableArray();
    }
    public long StepLimit { get; }
    public ImmutableArray<FixedPointMember> Members { get; }
}

public sealed class QueryCycleException(ImmutableArray<QueryAddress> cycle)
    : InvalidOperationException("未声明的查询环：" + string.Join(" -> ", cycle.Select(a => $"{a.Query.GetType().Name}[{a.Key}]")))
{
    public ImmutableArray<QueryAddress> Cycle { get; } = cycle;
}
