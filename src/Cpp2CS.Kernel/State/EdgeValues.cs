using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

/// <summary>某条入边下的读取位置视图；不消去原读取的内存版本或边身份。</summary>
public sealed record EdgeReadAtom(Term Original, Location Location, FlowEdge Edge) : AtomIdentity
{ public override string StableText => "state.edge-read"; }
public readonly record struct EdgeValueKey(Term Value, FlowEdge Edge);
public sealed class EdgeValueQuery(StateQueries state) : Query<EdgeValueKey, Term>
{
    private readonly ReadLocationQuery reads = new(state);
    public override Outcome<Term> Compute(QueryContext c, EdgeValueKey key)
    {
        var resolved = c.Get(state.Resolve, key.Value); if (!resolved.IsSuccess) return resolved;
        var term = resolved.Value; var t = c.Snapshot.Terms;
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<Term>();
        if (!index.Value.Predecessors.TryGetValue(key.Edge.Target,out var predecessors) || !predecessors.Any(p=>p.Block==key.Edge.Source))
            return Outcome<Term>.Failure(new("state.edge", "投影边不属于快照。"));
        if (term.Identity is ResultAtom { Definition: MergeIdentity id })
        {
            var merge = index.Value.Blocks[key.Edge.Target].Merges.FirstOrDefault(m => m.Identity == id);
            if (merge is not null)
            {
                var input = merge.Inputs.Single(i => i.Predecessor == key.Edge.Source);
                return c.Get(state.Resolve, input.Value);
            }
        }
        if (term.Identity is MemoryAtom or MemoryMerge or EdgeReadAtom)
        {
            var read = c.Get(reads, term); if (!read.IsSuccess) return read.Propagate<Term>();
            var root = c.Get(this, new(read.Value.Root, key.Edge)); if (!root.IsSuccess) return root;
            Term? address = read.Value.UnknownOffsetAddress;
            if (address is not null)
            {
                var projected = c.Get(this, new(address, key.Edge)); if (!projected.IsSuccess) return projected;
                address = projected.Value;
            }
            var location = read.Value with { Root = root.Value, UnknownOffsetAddress = address };
            return Outcome<Term>.Success(location == read.Value ? term : t.Atom(new EdgeReadAtom(term, location, key.Edge), term.Width));
        }
        if (term.Operands.IsEmpty) return Outcome<Term>.Success(term);
        var operands = new Term[term.Operands.Length];
        for (int i=0;i<operands.Length;i++)
        {
            var value=c.Get(this,new(term.Operands[i],key.Edge)); if (!value.IsSuccess) return value;
            operands[i]=value.Value;
        }
        return Outcome<Term>.Success(term.Kind switch
        {
            TermKind.Operation => t.Apply(term.Operator!,term.Width,operands),
            TermKind.Slice => t.Slice(operands[0],term.SliceLow!.Value,term.Width),
            TermKind.Concat => t.Concat(operands), _ => term
        });
    }
}

public readonly record struct IncomingValuesKey(Term Value, BlockIdentity Block);
/// <summary>只分解依赖当前非循环汇合点参数的值；循环保持原来的不动点身份。</summary>
public sealed class IncomingValuesQuery(StateQueries state) : Query<IncomingValuesKey, ImmutableArray<MergeEdge>>
{
    private readonly EdgeValueQuery project = new(state);
    private readonly ReadLocationQuery reads = new(state);
    private readonly FlowQueries flow = new();
    public override Outcome<ImmutableArray<MergeEdge>> Compute(QueryContext c, IncomingValuesKey key)
    {
        var index=c.Get(state.Index,0); if (!index.IsSuccess) return index.Propagate<ImmutableArray<MergeEdge>>();
        var block=index.Value.Blocks[key.Block];
        if (block.Merges.IsEmpty) return Outcome<ImmutableArray<MergeEdge>>.Success([]);
        var ids=block.Merges.Select(m=>m.Identity).ToHashSet();
        var pending=new Stack<Term>(); var seen=new HashSet<Term>(); pending.Push(key.Value); bool depends=false;
        while (pending.TryPop(out var term))
        {
            var resolved=c.Get(state.Resolve,term); if (!resolved.IsSuccess) return resolved.Propagate<ImmutableArray<MergeEdge>>();
            term=resolved.Value;
            if (!seen.Add(term)) continue;
            if (c.Step() is { } why) return Outcome<ImmutableArray<MergeEdge>>.Failure(why);
            if (term.Identity is ResultAtom { Definition: MergeIdentity id } && ids.Contains(id)) { depends=true; break; }
            if (term.Identity is MemoryAtom or MemoryMerge or EdgeReadAtom)
            {
                var read=c.Get(reads,term); if (!read.IsSuccess) continue;
                pending.Push(read.Value.Root);
                if (read.Value.UnknownOffsetAddress is { } address) pending.Push(address);
            }
            foreach (var operand in term.Operands) pending.Push(operand);
        }
        if (!depends) return Outcome<ImmutableArray<MergeEdge>>.Success([]);
        var inputs=ImmutableArray.CreateBuilder<MergeEdge>();
        foreach (var p in index.Value.Predecessors[key.Block])
        {
            var dominates=c.Get(flow.Dominates,new(key.Block,p.Block)); if (!dominates.IsSuccess) return dominates.Propagate<ImmutableArray<MergeEdge>>();
            if (dominates.Value) return Outcome<ImmutableArray<MergeEdge>>.Success([]);
            var value=c.Get(project,new(key.Value,new(p.Block,key.Block))); if (!value.IsSuccess) return value.Propagate<ImmutableArray<MergeEdge>>();
            inputs.Add(new(p.Block,p.Before,value.Value));
        }
        return Outcome<ImmutableArray<MergeEdge>>.Success(inputs.ToImmutable());
    }
}
