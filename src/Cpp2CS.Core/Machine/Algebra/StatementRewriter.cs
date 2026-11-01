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

    /// <summary>
    /// 写许可：非空时，挂接到本改写器的语句序列禁止写入，值为关闭时所在的阶段或步骤。方法会话在分析步骤、下降与证明期间关闭；
    /// 没有挂接的语句序列（会话之外的函数、尚未挂接的新块）不受影响。
    /// </summary>
    public string? Closed { get; set; }

    /// <summary>写入之前的检查：写许可关闭时按内部错误抛出。</summary>
    internal void Writing()
    {
        if (Closed is not null)
            throw new InvalidOperationException($"写许可已关闭（{Closed}）：机器 IR 的语句在此期间不得写入");
    }

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

/// <summary>“调用 + 参数序号”键：调用按引用比较。</summary>
internal sealed class CallParameterKeys : IEqualityComparer<(Call Call, int Parameter)>
{
    public static readonly CallParameterKeys Instance = new();

    public bool Equals((Call Call, int Parameter) x, (Call Call, int Parameter) y) => ReferenceEquals(x.Call, y.Call) && x.Parameter == y.Parameter;

    public int GetHashCode((Call Call, int Parameter) obj) => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(obj.Call), obj.Parameter);
}
