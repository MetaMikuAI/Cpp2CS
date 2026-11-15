using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Binding;

public sealed record ParameterRead(bool IsRead, Reason? Reason = null);
/// <summary>被调方入口值的使用摘要；隐藏的方法信息形参不在摘要中。</summary>
public sealed record ParameterReads(ParameterRead? This, ImmutableArray<ParameterRead> Parameters)
{
    public static Outcome<ParameterReads> Prove(NativeFunction function, SignatureBinding signature, MethodBinder binder,
        CallNamingQuery calls, StateQueries state)
        => state.CreateContext(function).Get(new ReadsQuery(signature, binder, calls, state), 0);

    private sealed class ReadsQuery(SignatureBinding signature, MethodBinder binder, CallNamingQuery calls, StateQueries state)
        : Query<int, ParameterReads>(1_000_000)
    {
        public override Outcome<ParameterReads> Compute(QueryContext c, int key)
        {
            Outcome<ParameterReads> No(string code, string message, Reason? cause = null) =>
                Outcome<ParameterReads>.Failure(new("binding.parameter-reads." + code, message, cause));
            if (signature.Managed is not { } managed) return No("signature", "入口没有完整的托管形参绑定。");
            var uses = new SemanticUses(c, calls, state, binder, signature);
            var parameters = managed.ParameterIndices.Select((index, i) => (Index: index, Managed: i))
                .Concat(managed.ThisIndex is { } self ? [(self, -1)] : []).ToArray();
            var results = new Dictionary<int, ParameterRead>();
            foreach (var (index, number) in parameters)
            {
                var bound = binder.Parameter(signature, index, c.Snapshot.Terms, c.Snapshot.Inputs, c.Snapshot.IncomingArgumentArea);
                if (bound.Value is not { } value) return No("binding", "形参入口绑定失败：" + bound.Failure!.Detail);
                var ranges = new List<(Term Value, int Low, int Width)>();
                var stack = new List<Location>();
                Reason? missing = null;
                void Source(BoundSource? source)
                {
                    switch (source)
                    {
                        case TermSource term:
                            uses.Visit(term.Term, (part, low, width) =>
                            { if (part.Identity is EntryAtom) ranges.Add((part, low, width)); });
                            break;
                        case PiecesSource pieces:
                            foreach (var piece in pieces.Pieces) Source(piece.Source);
                            break;
                        case IndirectSource indirect: Source(indirect.Address); break;
                        case StackSource slot:
                            var address = c.Get(state.Resolve, slot.Area);
                            if (!address.IsSuccess) { missing = address.Why; break; }
                            var location = c.Get(state.Locations, new(address.Value, slot.Length * 8));
                            if (!location.IsSuccess) { missing = location.Why; break; }
                            stack.Add(location.Value with { Offset = location.Value.Offset + slot.Offset });
                            break;
                        case null when value.Type.Size == 0: break;
                        default: missing = new("binding.parameter-reads.source", "形参入口来源没有可查询的值。"); break;
                    }
                }
                Source(value.Source);
                if (missing is not null) return No("source", "形参入口项无法建立。", missing);
                Reason? read = null;
                foreach (var use in uses.Roots)
                {
                    if (c.Step() is { } why) return Outcome<ParameterReads>.Failure(why);
                    uses.Visit(use.Value, (term, low, width) =>
                    {
                        if (ranges.Any(range => range.Value == term && low < range.Low + range.Width && range.Low < low + width))
                            read ??= new("binding.parameter-reads.read", "形参被读：" + use.Kind + "。");
                    });
                    if (read is not null) break;
                }
                // 栈上传入的值由状态模型定位；帧地址逃逸或任一读取相交时，保守地视为已读。
                if (read is null && stack.Count != 0)
                {
                    var escapes = c.Get(state.Escapes, 0);
                    if (!escapes.IsSuccess) return No("escape", "栈形参的地址逃逸无法判定。", escapes.Why);
                    if (stack.Any(escapes.Value.MayReach)) read = new("binding.parameter-reads.read", "形参被读：栈形参地址可能逃逸。");
                    foreach (var load in c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>())
                    {
                        if (read is not null) break;
                        var address = c.Get(state.Resolve, load.Address);
                        if (!address.IsSuccess) return No("address", "读取地址无法解析。", address.Why);
                        var location = c.Get(state.Locations, new(address.Value, load.Width));
                        if (!location.IsSuccess) return No("location", "读取位置无法确定。", location.Why);
                        foreach (var slot in stack)
                        {
                            var overlap = c.Get(state.Alias, new(slot, location.Value));
                            if (!overlap.IsSuccess) return No("alias", "读取与栈形参的重叠无法判定。", overlap.Why);
                            if (overlap.Value.Kind != AliasKind.Disjoint)
                                read = new("binding.parameter-reads.read", "形参被读：读取可能触及栈形参。");
                        }
                    }
                }
                results[number] = new(read is not null, read);
            }
            return Outcome<ParameterReads>.Success(new(results.GetValueOrDefault(-1),
                [.. Enumerable.Range(0, managed.ParameterIndices.Length).Select(i => results[i])]));
        }
    }
}

public interface IParameterReadsSource
{
    Outcome<ParameterReads> Get(ulong entry, Cpp2CS.Model.MethodRef method);
}
