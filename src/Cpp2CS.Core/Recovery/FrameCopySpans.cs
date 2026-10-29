using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Memory;

namespace Cpp2CS.Recovery;

internal static class FrameCopySpans
{
    internal static IEnumerable<(long Offset, int Size)> Read(MachineFunction function) => CopySpans.Read(function);

    /// <summary>整值复制只能从连续写入组的首条开始；读取、调用及其他写入不能跨过。</summary>
    internal static Store? WriteStart(IReadOnlyList<Stmt> statements, IEnumerable<Store> stores)
    {
        var group = stores.ToHashSet<Stmt>(ReferenceEqualityComparer.Instance);
        if (group.Count == 0) return null;
        var start = -1;
        for (var i = 0; i < statements.Count; i++)
            if (group.Contains(statements[i])) { start = i; break; }
        if (start < 0 || start + group.Count > statements.Count) return null;
        for (var i = start; i < start + group.Count; i++)
            if (!group.Contains(statements[i])) return null;
        return (Store)statements[start];
    }
}
