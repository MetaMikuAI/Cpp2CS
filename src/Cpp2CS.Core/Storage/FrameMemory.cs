using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Ssa;

namespace Cpp2CS.Memory;

internal sealed record StatementSite(Stmt Statement, Block Block, int Index);
internal sealed record FrameSnapshotValue(MemoryVersion Version, Store Store, Use Value, IReadOnlyList<StatementSite> Reads);

/// <summary>帧读写的共同索引；快照证明保留原 SSA 值及全部读取位置。</summary>
internal sealed class FrameMemory(MachineFunction function)
{
    public StatementSite[] Sites { get; } = function.Blocks
        .SelectMany(b => b.Statements.Select((s, i) => new StatementSite(s, b, i))).ToArray();
    private Dominators? dominators;

    public RewriteResult<FrameSnapshotValue> Snapshot(StatementSite site)
    {
        if (site.Statement is not Store { Target: FrameAddress { Offset: < 0 } frame, Value: Use { Width: 64 or 128 } value } store)
            return RewriteResult<FrameSnapshotValue>.NoMatch();
        var range = new StorageRange(frame.Offset, value.Width / 8);
        var reads = new List<StatementSite>();
        var readCount = 0;
        bool Safe(Expr expression)
        {
            if (expression is Load { Address: FrameAddress from } load)
            {
                if (!range.Overlaps(new(from.Offset, load.Width / 8))) return true;
                if (from.Offset != frame.Offset || load.Width != value.Width) return false;
                readCount++;
                return true;
            }
            // 指向片段之前的地址也可能被递增后使用，保留原有保守逃逸边界。
            if (expression is FrameAddress address) return address.Offset >= range.End;
            return ExprMap.Children(expression).All(Safe);
        }
        foreach (var use in Sites)
        {
            if (ReferenceEquals(use.Statement, store)) continue;
            var before = readCount;
            if (use.Statement is Store { Target: FrameAddress target } other)
            {
                if (range.Overlaps(new(target.Offset, other.Value.Width / 8)))
                    return RewriteResult<FrameSnapshotValue>.Blocked("storage.overlapping-write", $"0x{other.Address:x} 存在重叠写入");
                if (!Safe(other.Value)) return RewriteResult<FrameSnapshotValue>.Blocked("storage.escape", $"0x{other.Address:x} 地址逃逸或读取范围不符");
            }
            else if (!ExprMap.Operands(use.Statement).All(Safe))
                return RewriteResult<FrameSnapshotValue>.Blocked("storage.escape", $"0x{use.Statement.Address:x} 地址逃逸或读取范围不符");
            if (readCount == before) continue;
            dominators ??= Dominators.Compute(function);
            if (use.Block == site.Block ? use.Index <= site.Index : !dominators.Dominates(site.Block.Index, use.Block.Index))
                return RewriteResult<FrameSnapshotValue>.Blocked("storage.uninitialized-path", $"0x{use.Statement.Address:x} 读取不受写入支配");
            reads.Add(use);
        }
        if (reads.Count == 0) return RewriteResult<FrameSnapshotValue>.NoMatch();
        var storage = new FrameStorage(function.Entry, range, store.Address);
        return RewriteResult<FrameSnapshotValue>.Applied(new(new(storage, store.Address), store, value, reads),
            new("storage.single-write-snapshot", reads.Select(r => r.Statement.Address).Prepend(store.Address).ToArray(),
                ["单次写入", "读取区间完整一致", "写入支配全部读取", "地址不逃逸", "复用原 SSA 值"]));
    }
}
