using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;

/// <summary>以语句身份为键的证据表（随操作的证据，副本共享）：身份离开函数时由编辑器通知迁移或删除。</summary>
internal interface IStatementKeyed
{
    void Replace(Stmt previous, Stmt? replacement);
}

/// <summary>以语句对象为键的证据表（随实例的证据，例如每个调用副本各自的解析结果）：每次对象被替换都由编辑器通知迁移。</summary>
internal interface IStatementInstances
{
    void Rewritten(Stmt previous, Stmt replacement);
}

/// <summary>
/// 机器函数的编辑器：函数中语句与块的全部修改都经过它（语句序列与块列表在写入时找到所属函数的编辑器）。
/// 负责写许可、IR 版本与证据通知。通知按语句身份：一个身份的最后一条语句离开函数时，通知观察者把它的证据
/// 迁移到替换它的语句上（身份不同时）或删除；同一身份仍有语句在函数中（改写、副本）时不通知。
/// </summary>
internal sealed class MachineEditor
{
    private IReadOnlyList<IStatementKeyed> tables = [];
    private Action<Stmt, Stmt?>? diagnostics;
    private readonly Dictionary<long, int> live = [];

    /// <summary>IR 版本：语句或块每有一次变化递增。</summary>
    public int Version { get; private set; }

    /// <summary>写许可：非空时禁止修改本函数的语句，值为关闭时所在的阶段或步骤（方法会话在分析步骤、下降与证明期间关闭）。</summary>
    public string? Closed { get; set; }

    /// <summary>登记证据表与洞账本，之后身份离开函数时通知它们。</summary>
    internal void Observe(IReadOnlyList<IStatementKeyed> tables, Action<Stmt, Stmt?>? diagnostics) => (this.tables, this.diagnostics) = (tables, diagnostics);

    /// <summary>写入之前的检查：写许可关闭时按内部错误抛出。</summary>
    internal void Writing()
    {
        if (Closed is not null)
            throw new InvalidOperationException($"写许可已关闭（{Closed}）：机器 IR 的语句在此期间不得写入");
    }

    internal void Entered(Stmt statement)
    {
        live[statement.Id] = live.GetValueOrDefault(statement.Id) + 1;
        Version++;
    }

    internal void Left(Stmt statement, Stmt? replacement)
    {
        if (replacement is not null)
            foreach (var table in tables)
                if (table is IStatementInstances instances) instances.Rewritten(statement, replacement);
        var count = live.GetValueOrDefault(statement.Id) - 1;
        if (count > 0) live[statement.Id] = count;
        else live.Remove(statement.Id);
        Version++;
        if (count <= 0 && (replacement is null || replacement.Id != statement.Id))
            Notify(statement, replacement);
    }

    internal void Changed() => Version++;

    /// <summary>不改 IR，只通知观察者：把 <paramref name="previous"/> 的证据交给 <paramref name="replacement"/>。</summary>
    public void Preserve(Stmt previous, Stmt replacement) => Notify(previous, replacement);

    private void Notify(Stmt previous, Stmt? replacement)
    {
        foreach (var table in tables) table.Replace(previous, replacement);
        diagnostics?.Invoke(previous, replacement);
    }

    public void Replace(Block block, int index, Stmt replacement) => block.Statements[index] = replacement;
    public void Replace(Block block, Index index, Stmt replacement) => Replace(block, index.GetOffset(block.Statements.Count), replacement);
    public void Insert(Block block, int index, Stmt statement) => block.Statements.Insert(index, statement);

    /// <summary>删除块中的这条语句（按对象定位，不按值相等）。</summary>
    public bool Remove(Block block, Stmt statement)
    {
        var index = block.Statements.FindIndex(s => ReferenceEquals(s, statement));
        if (index < 0) return false;
        block.Statements.RemoveAt(index);
        return true;
    }

    public void RemoveAt(Block block, int index) => block.Statements.RemoveAt(index);
    public int RemoveAll(Block block, Predicate<Stmt> predicate) => block.Statements.RemoveAll(predicate);
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

/// <summary>“调用 + 参数序号”键：调用按稳定身份比较。</summary>
internal sealed class CallParameterKeys : IEqualityComparer<(Call Call, int Parameter)>
{
    public static readonly CallParameterKeys Instance = new();

    public bool Equals((Call Call, int Parameter) x, (Call Call, int Parameter) y) => StatementIdentity.Instance.Equals(x.Call, y.Call) && x.Parameter == y.Parameter;

    public int GetHashCode((Call Call, int Parameter) obj) => HashCode.Combine(StatementIdentity.Instance.GetHashCode(obj.Call), obj.Parameter);
}
