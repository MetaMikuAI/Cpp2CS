using Cpp2CS.Model;

namespace Cpp2CS.IR;

public sealed record BlockId(string Name);
public enum EdgeKind { Normal, True, False, Exceptional }
public sealed record Edge(BlockId From, BlockId To, EdgeKind Kind);
public abstract record Operation(Evidence Evidence);
public sealed record LoadOperation(string Result, StorageAddress Address, int Bytes, string MemoryVersion, Evidence Origin) : Operation(Origin);
public sealed record StoreOperation(StorageAddress Address, Bits Value, string InputMemory, string OutputMemory, Evidence Origin) : Operation(Origin);
public sealed record CallOperation(CallSite Call, CallEffects Effects, Evidence Origin) : Operation(Origin);
public sealed record OpaqueOperation(string Description, bool MayWriteMemory, bool MayThrow, Evidence Origin) : Operation(Origin);
public abstract record Terminator;
public sealed record Jump(BlockId Target) : Terminator;
public sealed record Conditional(Bits Condition, BlockId True, BlockId False) : Terminator;
public sealed record Return(Bits? Value) : Terminator;
public sealed record Throw(Bits Exception) : Terminator;
public sealed record Invoke(CallOperation Call, BlockId? Normal, BlockId? Exceptional) : Terminator;
public sealed record BasicBlock(BlockId Id, Sequence<Operation> Operations, Terminator Exit);

public sealed class ControlFlowGraph
{
    public BlockId Entry { get; }
    public Sequence<BasicBlock> Blocks { get; }
    public Sequence<Edge> Edges { get; }
    public ControlFlowGraph(BlockId entry, IEnumerable<BasicBlock> blocks)
    {
        Entry = entry;
        Blocks = new(blocks);
        var ids = Blocks.Select(b => b.Id).ToHashSet();
        if (ids.Count != Blocks.Count || !ids.Contains(entry)) throw new ArgumentException("重复基本块或缺少入口");
        var edges = new List<Edge>();
        foreach (var block in Blocks)
        {
            if (block.Operations.Any(op => op is CallOperation { Effects.MayThrow: true } or OpaqueOperation { MayThrow: true }))
                throw new ArgumentException("可抛异常操作必须显式终止基本块；不支持操作不能隐藏异常边");
            switch (block.Exit)
            {
                case Jump j: edges.Add(new(block.Id, j.Target, EdgeKind.Normal)); break;
                case Conditional c:
                    if (c.Condition.Width != 1) throw new ArgumentException("分支条件必须是单比特");
                    edges.Add(new(block.Id, c.True, EdgeKind.True));
                    edges.Add(new(block.Id, c.False, EdgeKind.False));
                    break;
                case Invoke i:
                    if (i.Call.Effects.NoReturn && i.Normal is not null) throw new ArgumentException("不返回的调用不能有正常后继");
                    if (!i.Call.Effects.NoReturn && i.Normal is null) throw new ArgumentException("调用缺少正常后继");
                    if (i.Call.Effects.MayThrow != (i.Exceptional is not null)) throw new ArgumentException("异常出口必须显式表示，包括离开函数的出口");
                    if (i.Normal is not null) edges.Add(new(block.Id, i.Normal, EdgeKind.Normal));
                    if (i.Exceptional is not null) edges.Add(new(block.Id, i.Exceptional, EdgeKind.Exceptional));
                    break;
            }
        }
        if (edges.Any(e => !ids.Contains(e.To))) throw new ArgumentException("后继基本块不存在");
        Edges = new(edges);
    }
    public IReadOnlySet<BlockId> Reachable()
    {
        var seen = new HashSet<BlockId>();
        var pending = new Queue<BlockId>();
        pending.Enqueue(Entry);
        while (pending.TryDequeue(out var block))
        {
            if (!seen.Add(block)) continue;
            foreach (var edge in Edges.Where(e => e.From == block)) pending.Enqueue(edge.To);
        }
        return seen;
    }
}
