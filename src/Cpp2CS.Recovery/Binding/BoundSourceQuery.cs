using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Recovery.Binding;

public readonly record struct BoundSourceRequest(BoundSource? Source, Point Point);

/// <summary>把 ABI 绑定中的栈槽与分片解析为同一使用点的项；内存定义只由状态模型提供。</summary>
public sealed class BoundSourceQuery(StateQueries state) : Query<BoundSourceRequest, Term>
{
    public override Outcome<Term> Compute(QueryContext context, BoundSourceRequest key)
    {
        switch (key.Source)
        {
            case TermSource term: return Outcome<Term>.Success(term.Term);
            case StackSource stack:
                var address = context.Get(state.Resolve, stack.Area);
                if (!address.IsSuccess) return address;
                var location = context.Get(state.Locations, new(address.Value, stack.Length * 8));
                if (!location.IsSuccess) return location.Propagate<Term>();
                return context.Get(state.ValueAt, new(key.Point, location.Value with { Offset = location.Value.Offset + stack.Offset }));
            case PiecesSource pieces:
                var parts = new List<Term>(); int cursor = 0;
                foreach (var piece in pieces.Pieces.OrderBy(p => p.ValueOffset))
                {
                    if (piece.ValueOffset != cursor) return Outcome<Term>.Failure(new("binding.source", "实参分片包含填充或重叠"));
                    var part = context.Get(this, new(piece.Source, key.Point));
                    if (!part.IsSuccess) return part;
                    parts.Add(part.Value); cursor += piece.Length;
                }
                return Outcome<Term>.Success(context.Snapshot.Terms.Concat(parts.ToArray()));
            default: return Outcome<Term>.Failure(new("binding.source", "间接或无值实参尚未下降"));
        }
    }
}
