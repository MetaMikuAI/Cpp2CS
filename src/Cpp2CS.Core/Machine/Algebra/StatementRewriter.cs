using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;



internal interface IStatementKeyed
{
    void Replace(Stmt previous, Stmt? replacement);
}

/// <summary>集中修改语句序列，并将对象身份变更通知证据表。</summary>
internal sealed class StatementRewriter(IReadOnlyList<IStatementKeyed> tables, Action<Stmt, Stmt?>? diagnostics)
{
    public int Version { get; private set; }

    public void Preserve(Stmt previous, Stmt replacement)
    {
        foreach (var table in tables) table.Replace(previous, replacement);
        diagnostics?.Invoke(previous, replacement);
    }

    internal void Changed(Stmt? previous, Stmt? replacement)
    {
        if (previous is not null)
        {
            foreach (var table in tables) table.Replace(previous, replacement);
            diagnostics?.Invoke(previous, replacement);
        }
        Version++;
    }

    public void Attach(MachineFunction function)
    {
        foreach (var block in function.Blocks) block.Statements.Rewriter = this;
    }

    public void Replace(Block block, int index, Stmt replacement)
    {
        block.Statements.Rewriter = this;
        block.Statements[index] = replacement;
    }

    public void Replace(Block block, Index index, Stmt replacement) => Replace(block, index.GetOffset(block.Statements.Count), replacement);
    public void Insert(Block block, int index, Stmt statement) { block.Statements.Rewriter = this; block.Statements.Insert(index, statement); }
    public bool Remove(Block block, Stmt statement)
    {
        var index = block.Statements.IndexOf(statement);
        if (index < 0) return false;
        RemoveAt(block, index);
        return true;
    }

    public void RemoveAt(Block block, int index)
    {
        block.Statements.Rewriter = this;
        block.Statements.RemoveAt(index);
    }

    public int RemoveAll(Block block, Predicate<Stmt> predicate)
    {
        block.Statements.Rewriter = this;
        return block.Statements.RemoveAll(predicate);
    }
}

internal static class StatementKeys
{
    public static void Replace<TKey, TValue>(Dictionary<TKey, TValue> map, Stmt previous, Stmt? replacement) where TKey : Stmt
    {
        if (previous is not TKey key) return;
        if (replacement is TKey next && map.TryGetValue(key, out var value)) map[next] = value;
        if (replacement is null or Nop) map.Remove(key);
    }

    public static void Replace<T>(HashSet<T> set, Stmt previous, Stmt? replacement) where T : Stmt
    {
        if (previous is not T key) return;
        if (replacement is T next && set.Contains(key)) set.Add(next);
        if (replacement is null or Nop) set.Remove(key);
    }
}

/// <summary>
/// 复制块时，操作数未变的语句可能作为同一对象放进多个块；按引用为语句定位置的代码遇到这种语句时位置不唯一。
/// </summary>
internal static class SharedStatements
{
    /// <summary>序列中第一个重复出现的语句对象（按引用）；没有重复时为 null。</summary>
    public static Stmt? First(IEnumerable<Stmt> statements)
    {
        var seen = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        foreach (var statement in statements)
            if (!seen.Add(statement)) return statement;
        return null;
    }
}

/// <summary>
/// 值相等的语句键比较器：比较结果与默认比较器完全相同，另外统计结构相同而对象不同的键被判为相等的次数
/// （<see cref="Cpp2CS.Diagnostics.GateCounters.ValueEqualKeys"/>），作为改为引用相等之前的依据。
/// </summary>
internal sealed class ValueKeyProbe<T> : IEqualityComparer<T> where T : Stmt
{
    public static readonly ValueKeyProbe<T> Instance = new();

    public bool Equals(T? x, T? y)
    {
        var equal = EqualityComparer<T>.Default.Equals(x, y);
        if (equal && !ReferenceEquals(x, y)) Cpp2CS.Diagnostics.GateCounters.CountValueEqualKey();
        return equal;
    }

    public int GetHashCode(T obj) => EqualityComparer<T>.Default.GetHashCode(obj);
}

/// <summary><see cref="ValueKeyProbe{T}"/> 的“调用 + 参数序号”元组版本，只统计调用对象不同的情形。</summary>
internal sealed class CallParameterKeyProbe : IEqualityComparer<(Call Call, int Parameter)>
{
    public static readonly CallParameterKeyProbe Instance = new();

    public bool Equals((Call Call, int Parameter) x, (Call Call, int Parameter) y)
    {
        var equal = EqualityComparer<(Call Call, int Parameter)>.Default.Equals(x, y);
        if (equal && !ReferenceEquals(x.Call, y.Call)) Cpp2CS.Diagnostics.GateCounters.CountValueEqualKey();
        return equal;
    }

    public int GetHashCode((Call Call, int Parameter) obj) => EqualityComparer<(Call Call, int Parameter)>.Default.GetHashCode(obj);
}
