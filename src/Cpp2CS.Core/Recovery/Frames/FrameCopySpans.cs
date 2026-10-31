using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class FrameCopySpans
{
    internal static IEnumerable<(long Offset, int Size)> Read(MachineFunction function) => CopySpans.Read(function);

    /// <summary>调用前连续写入覆盖全部字段时，首条写入开始新的类型生命期。</summary>
    internal static Store? FullWriteBefore(IReadOnlyList<Stmt> statements, int before, long offset, int size,
        IReadOnlyList<(int Offset, int Size)> leaves, Func<Expr, long?> frameOffset)
    {
        if (size <= 0 || leaves.Count == 0) return null;
        var covered = new HashSet<long>();
        for (var i = before - 1; i >= 0; i--)
        {
            var statement = statements[i];
            if (statement is Store store)
            {
                if (frameOffset(store.Target) is not { } at || at < offset || at + store.Value.Width / 8 > offset + size) return null;
                for (var b = 0; b < store.Value.Width / 8; b++) covered.Add(at - offset + b);
                if (leaves.All(p => Enumerable.Range(p.Offset, p.Size).All(b => covered.Contains(b)))) return store;
                continue;
            }
            if (statement is not (Define or Nop)
                || ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => frameOffset(e) is { } at && at >= offset && at < offset + size)) return null;
        }
        return null;
    }

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
