using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>包装的实参对应以绑定后的 C 值记录；方法信息不作为托管实参。</summary>
public sealed record InternalCallForwarder(MethodRef Method, SignatureBinding Entry, SignatureBinding Native,
    ImmutableArray<int> Inputs)
{
    public ulong WrapperEntry { get; init; }

    public Call? Rewrite(MethodBinder binder, Call call, TermTable terms)
    {
        if (Bind(binder, call, terms).Value is not { } bound || Entry.Slots.Return.BufferAddress is not null) return null;
        var slots = new Dictionary<AbstractSlot, Term>();
        for (int i = 0; i < bound.Arguments.Length; i++)
        {
            if (bound.Arguments[i].Source is not TermSource source || Entry.Slots.Parameters[i].CopyAddress is not null) return null;
            foreach (var piece in Entry.Slots.Parameters[i].Pieces)
            {
                if (piece.Slot.Kind == SlotKind.ArgumentArea || piece.SlotOffset != 0 || slots.ContainsKey(piece.Slot)) return null;
                var value = terms.Slice(source.Term, piece.ValueOffset * 8, piece.Length * 8);
                slots.Add(piece.Slot, value.Width < 64 ? terms.Concat(value, terms.Constant(0, 64 - value.Width)) : value);
            }
        }
        return call with { Target = new ImageFunction(WrapperEntry), Arguments = slots.Select(s => new SlotValue(s.Key, s.Value)).ToImmutableArray() };
    }

    public BindingResult<BoundCall> Bind(MethodBinder binder, Call call, TermTable terms)
    {
        var actual = binder.Call(call, Native, terms);
        if (actual.Value is not { } bound) return actual;
        var arguments = Entry.Signature.Parameters.Select((type, i) => i == Entry.Managed!.MethodInformationIndex
            ? Inputs[i] >= 0 ? bound.Arguments[Inputs[i]] : new BoundValue(type, new TermSource(terms.Constant(0, type.Size * 8)), UnusedBitRule.Unspecified)
            : bound.Arguments[Inputs[i]]).ToImmutableArray();
        return new(new(Entry, arguments, bound.Result), null);
    }
}

/// <summary>多定义共享实现不提供身份；包装不纯时不会进入事实集合。</summary>
public sealed class InternalCallFacts(IEnumerable<(ulong Entry, InternalCallForwarder Forwarder)> direct,
    IEnumerable<(ulong Cache, InternalCallForwarder Forwarder)> caches)
{
    public ImmutableDictionary<ulong, InternalCallForwarder> Direct { get; } = Unique(direct);
    public ImmutableDictionary<ulong, InternalCallForwarder> Caches { get; } = Unique(caches);
    public ImmutableHashSet<ulong> AmbiguousEntries { get; } = direct.GroupBy(x => x.Entry)
        .Where(g => g.Select(x => x.Forwarder.Method.Method).Distinct().Count() > 1).Select(g => g.Key).ToImmutableHashSet();
    public int Ambiguous => AmbiguousEntries.Count;
    public static InternalCallFacts Empty { get; } = new([], []);
    private static ImmutableDictionary<ulong, InternalCallForwarder> Unique(IEnumerable<(ulong Key, InternalCallForwarder Forwarder)> values) =>
        values.GroupBy(x => x.Key).Where(g => g.Select(x => x.Forwarder.Method.Method).Distinct().Count() == 1
            && g.Skip(1).All(x => x.Forwarder.Native == g.First().Forwarder.Native && x.Forwarder.Inputs.SequenceEqual(g.First().Forwarder.Inputs)))
            .ToImmutableDictionary(g => g.Key, g => g.First().Forwarder);
}

/// <summary>一次事件、入口实参的固定双射、原样返回；值与支配关系由内核查询证明。</summary>
public static class InternalCallWrappers
{
    public static Outcome<InternalCallForwarder> Forwarder(MethodRef method, NativeFunction function, MethodBinder binder,
        StateQueries state, Call? selected = null, IReadOnlySet<Statement>? privateStatements = null)
    {
        Outcome<InternalCallForwarder> No(string code, string message) => Outcome<InternalCallForwarder>.Failure(new("icall.wrapper." + code, message));
        var calls = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().Where(s => privateStatements?.Contains(s) != true).ToArray();
        if (calls.Length != 1 || selected is not null && calls[0].Identity != selected.Identity || calls[0].DoesNotReturn || calls[0].Unwind is not null)
            return No("events", "包装不是恰好一次正常转发调用。");
        var call = calls[0];
        var signature = binder.Entry(method, BindingEntryKind.Ordinary).Value;
        if (signature?.Managed is not { } managed) return No("signature", "包装没有完整的封闭入口签名。");
        var c = state.CreateContext(function); var sources = new BoundSourceQuery(state); var flow = new FlowQueries();
        Outcome<Term> Value(BoundSource? source, Point at)
        {
            var value = c.Get(sources, new(source, at));
            return value.IsSuccess ? c.Get(state.Resolve, value.Value) : value;
        }
        var block = function.Blocks.Single(b => b.Statements.Contains(call)); var point = new Point(block.Identity, block.Statements.IndexOf(call));
        var returns = function.Blocks.Where(b => b.End is Return).ToArray();
        var graph = c.Get(flow.Graph, 0);
        if (returns.Length != 1 || !graph.IsSuccess || !graph.Value.Reachable.Contains(returns[0].Identity))
            return No("control", "包装没有唯一可达的返回；不把无返回循环当作转发。");
        foreach (var b in function.Blocks)
        {
            if (b.Handler is not null || !b.Merges.IsEmpty || b.End is not (Jump or Return)) return No("control", "包装仍含分支、合流或异常处理。");
            foreach (var s in b.Statements.Where(s => s is not Call && privateStatements?.Contains(s) != true))
            {
                if (s is not (MemoryRead or MemoryWrite)) return No("effects", "包装仍含其他事件。");
                var address = s is MemoryRead read ? read.Address : ((MemoryWrite)s).Address;
                int width = s is MemoryRead r ? r.Width : ((MemoryWrite)s).Width;
                var resolved = c.Get(state.Resolve, address);
                if (!resolved.IsSuccess || c.Get(state.Locations, new(resolved.Value, width)) is not { IsSuccess: true, Value.Region: Region.Frame })
                    return No("effects", "包装仍含非帧访问。");
            }
            if (b.End is Return && c.Get(flow.PointDominates, new(point, new(b.Identity, b.Statements.Length))) is not { IsSuccess: true, Value: true })
                return No("control", "转发调用不支配全部返回。");
        }
        // 从现场槽中找完整入口值；接收者、显式形参与用于填补槽位的方法信息使用同一个对应机制。
        var forwarded = new List<(int Input, CType Type, AbstractSlot Slot)>();
        var expectedInputs = new Dictionary<int, Term>();
        for (int i = 0; i < signature.Signature.Parameters.Length; i++)
        {
            if (signature.Signature.Parameters[i] is not (CInteger or CPointer or CFloat))
                return No("input-shape", "包装输入不是可逐值复核的标量；聚合形参保留为其他形状。");
            var input = binder.Parameter(signature, i, function.Terms, function.Inputs, function.IncomingArgumentArea).Value;
            var expected = input is null ? default : Value(input.Source, new(function.Entry, 0));
            if (!expected.IsSuccess || expected.Value.ContainsUndefined)
            {
                if (i == managed.MethodInformationIndex) continue;
                return No("arguments", "包装入口实参没有完整值。");
            }
            expectedInputs[i] = expected.Value;
            if (i == managed.MethodInformationIndex) continue;
            var kind = input!.Type is CFloat ? SlotKind.Floating : SlotKind.Integer;
            var matches = call.Arguments.Where(a => a.Slot.Kind == kind && a.Value.Width >= expected.Value.Width
                && c.Get(state.Resolve, function.Terms.Slice(a.Value, 0, expected.Value.Width)) is { IsSuccess: true } value && value.Value == expected.Value).ToArray();
            if (matches.Length != 1 || forwarded.Any(f => f.Slot == matches[0].Slot))
                return No("arguments", "调用实参不是入口实参的唯一完整对应。");
            forwarded.Add((i, input!.Type, matches[0].Slot));
        }
        foreach (var kind in new[] { SlotKind.Integer, SlotKind.Floating })
        {
            long last = forwarded.Where(f => f.Slot.Kind == kind).Select(f => f.Slot.Position).DefaultIfEmpty(-1).Max();
            for (long position = 0; position <= last; position++)
            {
                var slot = new AbstractSlot(kind, position);
                if (forwarded.Any(f => f.Slot == slot)) continue;
                if (kind != SlotKind.Integer || !expectedInputs.TryGetValue(managed.MethodInformationIndex, out var info)
                    || call.Arguments.SingleOrDefault(a => a.Slot == slot) is not { } argument || argument.Value.Width < info.Width
                    || c.Get(state.Resolve, function.Terms.Slice(argument.Value, 0, info.Width)) is not { IsSuccess: true } actualInfo || actualInfo.Value != info
                    || forwarded.Any(f => f.Input == managed.MethodInformationIndex))
                    return No("arguments", "实参槽的间隙不是包装实际传入的方法信息。");
                forwarded.Add((managed.MethodInformationIndex, signature.Signature.Parameters[managed.MethodInformationIndex], slot));
            }
        }
        var ordered = forwarded.OrderBy(f => f.Slot.Kind == SlotKind.Floating ? 1 : 0).ThenBy(f => f.Slot.Position).ToArray();
        var nativeSignature = binder.Classify(signature.Signature with { Parameters = ordered.Select(f => f.Type).ToImmutableArray() }).Value;
        if (nativeSignature is null || ordered.Where((f, i) => nativeSignature.Slots.Parameters[i].Pieces is not [{ Slot: var slot }] || slot != f.Slot).Any()
            || binder.Call(call, nativeSignature, function.Terms).Value is not { } actual)
            return No("binding", "现场实参对应不能由同一 ABI 签名完整表达。");
        var inputs = Enumerable.Repeat(-1, signature.Signature.Parameters.Length).ToArray();
        for (int j = 0; j < ordered.Length; j++) inputs[ordered[j].Input] = j;
        foreach (var b in function.Blocks.Where(b => b.End is Return))
        {
            var returned = binder.Return((Return)b.End, signature, function.Terms).Value;
            if (returned is null) return No("result", "包装的返回值不能绑定。");
            if (signature.Signature.ReturnType is CVoid) continue;
            var value = Value(returned.Source, new(b.Identity, b.Statements.Length));
            var result = Value(actual.Result.Source, point);
            if (!value.IsSuccess || !result.IsSuccess || value.Value != result.Value || value.Value.ContainsUndefined)
                return No("result", "包装没有原样返回调用结果。");
        }
        return Outcome<InternalCallForwarder>.Success(new(method, signature, nativeSignature, [.. inputs]));
    }
}
