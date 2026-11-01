using System.Collections;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Machine.Algebra;

/// <summary>块的语句序列。所属块在函数中时，所有写入都经函数的编辑器：先检查写许可，再登记身份的进出。</summary>
public sealed class StatementList : IList<Stmt>, IReadOnlyList<Stmt>
{
    private readonly List<Stmt> items = [];
    /// <summary>所属的块；块在函数中时经它找到编辑器。</summary>
    internal Block? Owner { get; set; }
    private MachineEditor? Editor => Owner?.Function?.Editor;
    public Stmt this[int index]
    {
        get => items[index];
        set
        {
            if (ReferenceEquals(items[index], value)) return;
            var editor = Editor;
            editor?.Writing();
            var previous = items[index];
            editor?.Entered(value);
            items[index] = value;
            editor?.Left(previous, value);
        }
    }
    public int Count => items.Count;
    public bool IsReadOnly => false;
    public void Add(Stmt item) { var editor = Editor; editor?.Writing(); items.Add(item); editor?.Entered(item); }
    public void AddRange(IEnumerable<Stmt> values) { foreach (var item in values) Add(item); }
    public void Insert(int index, Stmt item) { var editor = Editor; editor?.Writing(); items.Insert(index, item); editor?.Entered(item); }
    public void InsertRange(int index, IEnumerable<Stmt> values) { foreach (var item in values) Insert(index++, item); }
    public void RemoveAt(int index) { var editor = Editor; editor?.Writing(); var item = items[index]; items.RemoveAt(index); editor?.Left(item, null); }
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
