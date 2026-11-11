using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Kernel.Queries;

namespace Cpp2CS.Kernel.State;

public enum Region { Frame, Image, Thread, Other }
public sealed record Location(Region Region, Term Root, BigInteger? Offset, int Width, Term? UnknownOffsetAddress = null);
public readonly record struct AddressRequest(Term Address, int Width);
public sealed class LocationQuery : Query<AddressRequest, Location>
{
    public override Outcome<Location> Compute(QueryContext context, AddressRequest key)
    {
        if (key.Width <= 0 || key.Address.Width != context.Snapshot.AddressWidth || key.Address.Kind == TermKind.Undefined)
            return Outcome<Location>.Failure(new("state.address", "地址或访问位宽不合法。"));
        var term = key.Address; BigInteger? offset = 0;
        while (term.Operator is CoreOperator { Operation: CoreOperation.Add or CoreOperation.Subtract } op)
        {
            if (context.Step() is { } why) return Outcome<Location>.Failure(why);
            var a = term.Operands[0]; var b = term.Operands[1];
            if (b.ConstantValue is { } n) { offset += op.Operation == CoreOperation.Add ? n : -n; term = a; }
            else if (op.Operation == CoreOperation.Add && a.ConstantValue is { } m) { offset += m; term = b; }
            else
            {
                var left = context.Get(this, new(a, key.Width));
                if (!left.IsSuccess) return left;
                var root = left.Value;
                if (op.Operation == CoreOperation.Add)
                {
                    var right = context.Get(this, new(b, key.Width));
                    if (!right.IsSuccess) return right;
                    if (root.Region == Region.Other && right.Value.Region != Region.Other) root = right.Value;
                    else if (root.Region != Region.Other && right.Value.Region != Region.Other)
                        return Outcome<Location>.Failure(new("state.address-roots", "地址包含多个区域根，不能分解。"));
                }
                return Outcome<Location>.Success(root with { Offset = null, UnknownOffsetAddress = key.Address });
            }
        }
        if (offset is { } value)
        {
            var modulus = BigInteger.One << term.Width;
            value = (value % modulus + modulus) % modulus;
            offset = value >= modulus / 2 ? value - modulus : value;
        }
        var region = term.Identity is RootAtom r ? r.Kind switch
        { AddressRoot.Frame => Region.Frame, AddressRoot.Image => Region.Image, _ => Region.Thread } : Region.Other;
        return Outcome<Location>.Success(new(region, term, offset, key.Width, offset is null ? key.Address : null));
    }
}
public enum AliasKind { Overlap, Disjoint, Unknown }
public sealed record Overlap(AliasKind Kind, int LeftLow = 0, int RightLow = 0, int Width = 0);
public readonly record struct AliasRequest(Location Left, Location Right);
public sealed record EscapeInfo(BigInteger? Lowest, bool Any)
{
    public bool MayReach(Location location) => Any && (Lowest is null || location.Offset is null || location.Offset * 8 + location.Width > Lowest * 8);
}
public sealed class EscapeQuery(LocationQuery locations) : Query<int, EscapeInfo>
{
    public override Outcome<EscapeInfo> Compute(QueryContext context, int key)
    {
        var function = context.Snapshot; var pending = new Stack<Term>(); var seen = new HashSet<Term>();
        foreach (var b in function.Blocks)
        {
            foreach (var s in b.Statements)
                switch (s)
                {
                    case Call c: foreach (var a in c.Arguments) pending.Push(a.Value); if (c.Target is ComputedTarget t) pending.Push(t.Value); break;
                    case MemoryWrite w: pending.Push(w.Value); break;
                }
            if (b.End is Return r) foreach (var v in r.Results) pending.Push(v.Value);
        }
        BigInteger? lowest = null; bool any = false;
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term) || term.Kind == TermKind.Undefined) continue;
            if (context.Step() is { } why) return Outcome<EscapeInfo>.Failure(why);
            if (term.Width == function.AddressWidth)
            {
                var l = context.Get(locations, new(term, 1));
                if (!l.IsSuccess) return l.Propagate<EscapeInfo>();
                if (l.Value.Region == Region.Frame)
                {
                    if (l.Value.Offset is null) return Outcome<EscapeInfo>.Success(new(null, true));
                    lowest = lowest is null ? l.Value.Offset : BigInteger.Min(lowest.Value, l.Value.Offset.Value);
                    any = true; continue;
                }
            }
            foreach (var child in term.Operands) pending.Push(child);
            // 间接转送的地址按所有可能的存储来源取上界。
            if (term.Identity is ResultAtom { Definition: ReadIdentity })
                foreach (var w in function.Blocks.SelectMany(b => b.Statements).OfType<MemoryWrite>()) pending.Push(w.Value);
            if (term.Identity is ResultAtom { Definition: MergeIdentity id })
                foreach (var input in function.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs) pending.Push(input.Value);
        }
        return Outcome<EscapeInfo>.Success(new(lowest, any));
    }
}
public sealed class AliasQuery(EscapeQuery escapes) : Query<AliasRequest, Overlap>
{
    public override Outcome<Overlap> Compute(QueryContext context, AliasRequest key)
    {
        var (a, b) = key;
        Overlap result;
        if (a.Region != Region.Other && b.Region != Region.Other && a.Region != b.Region) result = new(AliasKind.Disjoint);
        else if (a.Root == b.Root && a.Offset is { } x && b.Offset is { } y)
        {
            var start = BigInteger.Max(x * 8, y * 8); var end = BigInteger.Min(x * 8 + a.Width, y * 8 + b.Width);
            result = end <= start ? new(AliasKind.Disjoint) : new(AliasKind.Overlap, (int)(start - x * 8), (int)(start - y * 8), (int)(end - start));
        }
        else if ((a.Region == Region.Frame && b.Region == Region.Other) || (b.Region == Region.Frame && a.Region == Region.Other))
        {
            var e = context.Get(escapes, 0); if (!e.IsSuccess) return e.Propagate<Overlap>();
            result = new(e.Value.MayReach(a.Region == Region.Frame ? a : b) ? AliasKind.Unknown : AliasKind.Disjoint);
        }
        else result = new(AliasKind.Unknown);
        return Outcome<Overlap>.Success(result);
    }
}

/// <summary>UnknownMemory 是未知读写上界；具体读取保留给效果使用者，不截断定义链。</summary>
public sealed record CallEffects(bool UnknownMemory, BigInteger? StackArgumentBytes, ImmutableArray<Location> Writes)
{
    public ImmutableArray<Location> Reads { get; init; } = [];
}
/// <summary>实现必须不可变；依赖其他分析时经 context.Get 取得。</summary>
public interface ICallEffectSource { Outcome<CallEffects> Get(QueryContext context, Call call); }
public sealed class UnknownCallEffects : ICallEffectSource
{
    public Outcome<CallEffects> Get(QueryContext context, Call call) => Outcome<CallEffects>.Success(new(true, null, []));
}
public sealed class CallEffectQuery(ICallEffectSource source) : Query<CallIdentity, CallEffects>
{
    public override Outcome<CallEffects> Compute(QueryContext context, CallIdentity key) => source.Get(context,
        context.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single(c => c.Identity == key));
}
