using System.Collections;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;

/// <summary>语句序列的所有写入都通知改写器，机器层辅助 pass 不会绕过身份键迁移。</summary>
public sealed class StatementList : IList<Stmt>, IReadOnlyList<Stmt>
{
    private readonly List<Stmt> items = [];
    internal StatementRewriter Rewriter { get; set; } = new([], null);
    public Stmt this[int index]
    {
        get => items[index];
        set { if (!ReferenceEquals(items[index], value)) { Rewriter.Changed(items[index], value); items[index] = value; } }
    }
    public int Count => items.Count;
    public bool IsReadOnly => false;
    public void Add(Stmt item) { items.Add(item); Rewriter.Changed(null, item); }
    public void AddRange(IEnumerable<Stmt> values) { foreach (var item in values) Add(item); }
    public void Insert(int index, Stmt item) { items.Insert(index, item); Rewriter.Changed(null, item); }
    public void InsertRange(int index, IEnumerable<Stmt> values) { foreach (var item in values) Insert(index++, item); }
    public void RemoveAt(int index) { var item = items[index]; items.RemoveAt(index); Rewriter.Changed(item, null); }
    public bool Remove(Stmt item) { var index = items.IndexOf(item); if (index < 0) return false; RemoveAt(index); return true; }
    public void RemoveRange(int index, int count) { for (var i = 0; i < count; i++) RemoveAt(index); }
    public int RemoveAll(Predicate<Stmt> predicate)
    {
        var removed = 0;
        for (var i = 0; i < Count; i++) if (predicate(items[i])) { RemoveAt(i--); removed++; }
        return removed;
    }
    public void Clear() => RemoveRange(0, Count);
    public bool Contains(Stmt item) => items.Contains(item);
    public int IndexOf(Stmt item) => items.IndexOf(item);
    public int FindIndex(Predicate<Stmt> predicate) => items.FindIndex(predicate);
    public int FindIndex(int start, Predicate<Stmt> predicate) => items.FindIndex(start, predicate);
    public int FindLastIndex(Predicate<Stmt> predicate) => items.FindLastIndex(predicate);
    public List<Stmt> GetRange(int index, int count) => items.GetRange(index, count);
    public Stmt[] ToArray() => items.ToArray();
    public void CopyTo(Stmt[] array, int arrayIndex) => items.CopyTo(array, arrayIndex);
    public IEnumerator<Stmt> GetEnumerator() => items.GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    public static implicit operator StatementList(List<Stmt> values) { var list = new StatementList(); list.AddRange(values); return list; }
}
