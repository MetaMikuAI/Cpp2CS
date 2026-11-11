using System.Numerics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

/// <summary>只证明读取位置一致，不证明各内存版本同值；使用者须另证不可变性。</summary>
public sealed class ReadLocationQuery(StateQueries state) : Query<Term, Location>
{
    public override Outcome<Location> Compute(QueryContext c, Term key)
    {
        var pending = new Stack<Term>(); var seen = new HashSet<Term>(); pending.Push(key);
        Location? result = null;
        while (pending.TryPop(out var term))
        {
            var resolved = c.Get(state.Resolve, term); if (!resolved.IsSuccess) return resolved.Propagate<Location>();
            term = resolved.Value;
            if (!seen.Add(term)) continue;
            if (c.Step() is { } why) return Outcome<Location>.Failure(why);
            if (term.Identity is MemoryMerge merge)
            {
                var inputs = c.Get(state.MergeInputs, merge); if (!inputs.IsSuccess) return inputs.Propagate<Location>();
                foreach (var input in inputs.Value) pending.Push(input.Value);
            }
            else if (term.Identity is ResultAtom { Definition: MergeIdentity id })
            {
                foreach (var input in c.Snapshot.Blocks.SelectMany(b=>b.Merges).Single(m=>m.Identity==id).Inputs) pending.Push(input.Value);
            }
            else if (term.Identity is MemoryAtom or EdgeReadAtom)
            {
                var location = term.Identity is MemoryAtom read ? read.Location : ((EdgeReadAtom)term.Identity).Location;
                if (result is not null && result != location) return No();
                result = location;
            }
            else return No();
        }
        return result is null ? No() : Outcome<Location>.Success(result);
    }
    private static Outcome<Location> No() => Outcome<Location>.Failure(new("state.read-location", "来源没有唯一完整的读取位置。"));
}

public readonly record struct StridedAddressKey(Term Address, long Stride);
public sealed record StridedAddress(Term Base, long Remainder);
/// <summary>有限合流方程的基址与模步长偏移；回边必须保持同一剩余类，且必须有外部基址。</summary>
public sealed class StridedAddressQuery(StateQueries state) : Query<StridedAddressKey, StridedAddress>
{
    public override Outcome<StridedAddress> Compute(QueryContext c, StridedAddressKey key)
    {
        // 模位宽溢出也必须保持模步长关系。
        if (key.Stride <= 0 || (BigInteger.One << key.Address.Width) % key.Stride != 0) return No();
        var pending = new Stack<(Term Term, long Offset)>(); pending.Push((key.Address, 0));
        var seen = new Dictionary<Term, long>(); StridedAddress? result = null;
        long Mod(BigInteger n) => (long)((n % key.Stride + key.Stride) % key.Stride);
        while (pending.TryPop(out var item))
        {
            if (c.Step() is { } why) return Outcome<StridedAddress>.Failure(why);
            var resolved = c.Get(state.Resolve, item.Term); if (!resolved.IsSuccess) return resolved.Propagate<StridedAddress>();
            var term = resolved.Value; var offset = item.Offset;
            if (seen.TryGetValue(term, out var prior)) { if (prior != offset) return No(); continue; }
            seen.Add(term, offset);
            if (term.Operator is CoreOperator { Operation: CoreOperation.Add or CoreOperation.Subtract } op && term.Operands[1].ConstantValue is { } n)
                pending.Push((term.Operands[0], Mod(offset + (op.Operation == CoreOperation.Add ? n : -n))));
            else if (term.Operator is CoreOperator { Operation: CoreOperation.Add } && Multiple(term.Operands[1], key.Stride))
                pending.Push((term.Operands[0], offset));
            else if (term.Operator is CoreOperator { Operation: CoreOperation.Add } && Multiple(term.Operands[0], key.Stride))
                pending.Push((term.Operands[1], offset));
            else if (term.Identity is ResultAtom { Definition: MergeIdentity id })
            {
                var inputs = c.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs;
                if (inputs.IsEmpty) return No();
                foreach (var input in inputs) pending.Push((input.Value, offset));
            }
            else
            {
                var candidate = new StridedAddress(term, offset);
                if (result is not null && result != candidate) return No();
                result = candidate;
            }
        }
        return result is null ? No() : Outcome<StridedAddress>.Success(result);
    }
    // 低零位或常量因子给出模步长为零的充分条件；不知道时不拆分地址。
    private static bool Multiple(Term term, long stride) =>
        term.ConstantValue is { } n && n % stride == 0 ||
        term.Kind == TermKind.Concat && term.Operands[0].ConstantValue == 0 && (BigInteger.One << term.Operands[0].Width) % stride == 0 ||
        term.Operator is CoreOperator { Operation: CoreOperation.Multiply } && term.Operands.Any(p=>p.ConstantValue is { } factor && factor % stride == 0);
    private static Outcome<StridedAddress> No() => Outcome<StridedAddress>.Failure(new("state.strided-address", "合流地址没有唯一基址或不能保持模步长偏移。"));
}
