using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Naming;

public sealed record InterfaceDataName(Term Object, Term Interface, long Slot, string Basis) : ValueName;
public readonly record struct InterfaceDataKey(Term Value, Point Point, string? Field = null, FlowEdge? Edge = null);

/// <summary>规格项的命名属于值命名；分派查询只消费名字，不识别查找循环。</summary>
/// <remarks>依据 vm/ClassInlines.h/.cpp::GetInterfaceInvokeDataFromVTable 与 VirtualInvokeData 布局。</remarks>
public sealed class InterfaceDataQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names, RuntimeSpec spec)
    : Query<InterfaceDataKey, InterfaceDataName>
{
    private readonly PathFactQuery facts = new(state);
    private readonly IncomingValuesQuery incomingValues = new(state);
    private readonly ExistingMergeQuery existingMerge = new(state);
    private readonly ReadLocationQuery reads = new(state);
    private readonly StridedAddressQuery strides = new(state);
    internal static InterfaceDataName Pending(Term value) => new(value, value, -1, "pending");
    internal static bool IsPending(InterfaceDataName name) => name.Slot == -1 && name.Basis == "pending";
    public override Outcome<InterfaceDataName> Compute(QueryContext c, InterfaceDataKey key)
    {
        var resolved = c.Get(state.Resolve, key.Value); if (!resolved.IsSuccess) return resolved.Propagate<InterfaceDataName>();
        var value = resolved.Value;
        if (key.Field is { } field)
        {
            var read = c.Get(reads, value);
            if (read.IsSuccess && read.Value.Width == c.Snapshot.AddressWidth)
            {
                var address = Add(c, Address(c, read.Value), -spec.Layout.Field("VirtualInvokeData", field).ByteOffset);
                return c.Get(this, key with { Value = address, Field = null });
            }
            if (value.Identity is not ResultAtom { Definition: MergeIdentity })
                return No("source", "来源不是调用数据字段的完整读取。", read.Why);
        }
        if (value.Identity is MemoryMerge memory)
        {
            var inputs = c.Get(state.MergeInputs, memory); if (!inputs.IsSuccess) return inputs.Propagate<InterfaceDataName>();
            return Merge(c, key, memory.Block, inputs.Value.Select(i => (i.Predecessor, i.Before, i.Value)));
        }
        if (value.Identity is ResultAtom { Definition: MergeIdentity id })
        {
            var block = c.Snapshot.Blocks.Single(b => b.Merges.Any(m => m.Identity == id));
            return Merge(c, key, block.Identity, block.Merges.Single(m => m.Identity == id).Inputs.Select(i =>
                (i.Predecessor, c.Snapshot.Blocks.Single(b => b.Identity == i.Predecessor).Statements.Length, i.Value)));
        }
        if (value.Identity is ResultAtom { Definition: CallIdentity call })
        {
            var result = c.Get(calls, call); if (!result.IsSuccess) return result.Propagate<InterfaceDataName>();
            if (result.Value.Operation?.Name != "LookupInterfaceData" || result.Value.Operation.Result.Kind != RuntimeValueKind.InvokeData ||
                result.Value.Result?.Source is not TermSource output || output.Term != value)
                return No("source", "调用结果没有接口调用数据的规格身份。");
            Term? Input(string name) => result.Value.Inputs?.GetValueOrDefault(name)?.Source is TermSource source
                ? c.Get(state.Resolve, source.Term) is { IsSuccess: true } r ? r.Value : null : null;
            var obj = Input("object"); var itf = Input("interface"); var slot = Input("slot");
            if (obj is null || itf is null || slot?.ConstantValue is not { } n || n < 0 || n > ushort.MaxValue)
                return No("slot", "运行时调用的对象、接口或槽号没有完整绑定：" + (obj is null ? "对象" : itf is null ? "接口" : "槽号不是常量") + "。");
            return Yes(new(obj, itf, (long)n, "LookupInterfaceData"));
        }
        var incoming = c.Get(incomingValues, new(value, key.Point.Block));
        if (!incoming.IsSuccess) return incoming.Propagate<InterfaceDataName>();
        if (!incoming.Value.IsEmpty)
            return Merge(c,key,key.Point.Block,incoming.Value.Select(i=>(i.Predecessor,i.Before,i.Value)));
        // 虚表地址 = klass + vtable + (读取 pair.offset + slot) * sizeof(VirtualInvokeData)。
        var parts = new List<Term>(); BigInteger constant = 0; Sum(value, parts, ref constant);
        foreach (var klass in parts)
        {
            var headerRead = c.Get(reads, klass);
            if (!headerRead.IsSuccess || headerRead.Value.Offset != spec.Layout.Field("Il2CppObject", "klass").ByteOffset) continue;
            var header = headerRead.Value;
            var named = c.Get(names, klass);
            if (named.IsSuccess && named.Value == NameLattice.Pending) return Yes(Pending(key.Value));
            if (!named.IsSuccess || named.Value.Name is not FieldName h || h.Field != spec.Layout.Field("Il2CppObject", "klass").Path) continue;
            var other = parts.Where(p => p != klass).ToArray(); if (parts.Count != 2 || other.Length != 1) continue;
            var scaled = other[0]; Term? index = null;
            if (scaled.Operator is CoreOperator { Operation: CoreOperation.ShiftLeft } && scaled.Operands[1].ConstantValue is { } shift && shift >= 0 && shift < 63 && (BigInteger.One << (int)shift) == spec.Layout.VtableSlotSize) index = scaled.Operands[0];
            if (scaled.Operator is CoreOperator { Operation: CoreOperation.Multiply })
                index = scaled.Operands[0].ConstantValue == spec.Layout.VtableSlotSize ? scaled.Operands[1] : scaled.Operands[1].ConstantValue == spec.Layout.VtableSlotSize ? scaled.Operands[0] : null;
            if (index is null && scaled.Kind == TermKind.Concat && scaled.Operands[0].ConstantValue == 0)
            {
                int bits = 0; long size = spec.Layout.VtableSlotSize;
                while (size > 1 && size % 2 == 0) { bits++; size /= 2; }
                if (size == 1 && bits > 0 && scaled.Operands[0].Width >= bits)
                    index = c.Snapshot.Terms.Slice(scaled, bits, scaled.Width-bits);
            }
            if (index is null) continue;
            if (index.Operator is CoreOperator { Operation: CoreOperation.SignExtend }) index = index.Operands[0];
            var indices = new List<Term>(); BigInteger slot = 0; Sum(index, indices, ref slot);
            if (indices.Count != 1) continue;
            var offset = indices[0];
            if (offset.Operator is CoreOperator { Operation: CoreOperation.SignExtend }) offset = offset.Operands[0];
            var offsetRead = c.Get(reads, offset);
            if (!offsetRead.IsSuccess || offsetRead.Value.Width != spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair", "offset").Size * 8) continue;
            var pairOffset = offsetRead.Value;
            var relative = constant - spec.Layout.Field("Il2CppClass", "vtable").ByteOffset;
            if (relative % spec.Layout.VtableSlotSize != 0) continue;
            slot += relative / spec.Layout.VtableSlotSize;
            if (slot < 0 || slot > ushort.MaxValue) return No("slot", "接口槽号不是可表示的常量。");
            var pair = Add(c, Address(c, pairOffset), -spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair", "offset").ByteOffset);
            var stride = spec.Layout.Record("Il2CppRuntimeInterfaceOffsetPair").Size;
            var origin = c.Get(strides, new(pair, stride));
            if (!origin.IsSuccess || origin.Value.Remainder != 0) return No("table-origin", "偏移字段的地址没有对齐的表项来源。", origin.Why);
            var tableRead = c.Get(reads, origin.Value.Base);
            if (!tableRead.IsSuccess || tableRead.Value.Root != klass || tableRead.Value.Width != c.Snapshot.AddressWidth ||
                tableRead.Value.Offset != spec.Layout.Field("Il2CppClass", "interfaceOffsets").ByteOffset)
                return No("table-owner", "表项基址不是同一对象类的接口偏移表。", tableRead.Why);
            var interfaceAddress = Add(c, pair, spec.Layout.Field("Il2CppRuntimeInterfaceOffsetPair", "interfaceType").ByteOffset);
            // 同一表项的两个不可变规格字段；读取视图不把任意内存版本判为同值。
            foreach (var branch in c.Snapshot.Blocks.Select(b => b.End).OfType<Branch>())
            {
                var condition = c.Get(state.Resolve, branch.Condition); if (!condition.IsSuccess) continue;
                var equality = condition.Value;
                while (equality.Operator is CoreOperator { Operation: CoreOperation.Not }) equality = equality.Operands[0];
                if (equality.Operator is not CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual }) continue;
                for (int i = 0; i < 2; i++)
                {
                    var candidate = equality.Operands[i];
                    var candidateRead = c.Get(reads, candidate);
                    if (!candidateRead.IsSuccess || Address(c, candidateRead.Value) != interfaceAddress || candidateRead.Value.Width != c.Snapshot.AddressWidth) continue;
                    var equal = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, candidate, equality.Operands[1-i]);
                    var truth = c.Get(facts, new(key.Point, equal, key.Edge)); if (!truth.IsSuccess) return truth.Propagate<InterfaceDataName>();
                    if (truth.Value == PathTruth.True) return Yes(new(header.Root, equality.Operands[1-i], (long)slot, "ClassInlines::GetInterfaceInvokeDataFromVTable"));
                }
            }
            return No("path-fact", "路径事实不能证明表项接口等于所请求接口。");
        }
        return No("source", "来源不是登记的接口快路径或慢路径。");
    }
    private Outcome<InterfaceDataName> Merge(QueryContext c, InterfaceDataKey key, BlockIdentity block, IEnumerable<(BlockIdentity Source, int Before, Term Value)> inputs)
    {
        InterfaceDataName? answer = null;
        var receivers = ImmutableArray.CreateBuilder<Incoming>();
        foreach (var input in inputs)
        {
            var found = c.Get(this, new(input.Value, new(input.Source, input.Before), key.Field, new(input.Source, block)));
            if (!found.IsSuccess) return found;
            if (IsPending(found.Value)) return Yes(Pending(key.Value));
            if (answer is not null)
            {
                if (answer.Slot != found.Value.Slot) return No("merge-slot", "合流来源的槽号不一致。");
                var same = Compare(c, answer with { Object = found.Value.Object }, found.Value);
                if (!same.IsSuccess) return same.Propagate<InterfaceDataName>();
                if (same.Value is null) return Yes(Pending(key.Value));
                if (same.Value != true) return No("merge-interface", "合流来源的接口不一致。");
            }
            receivers.Add(new(input.Source, found.Value.Object));
            answer = found.Value;
        }
        if (answer is null) return No("source", "合流没有来源。");
        if (receivers.Any(r => r.Value != answer.Object))
        {
            var joined = c.Get(existingMerge, new(block, receivers.ToImmutable()));
            if (!joined.IsSuccess) return No("merge-object", "对象来源没有逐入边对应的已有合流。", joined.Why);
            answer = answer with { Object = joined.Value };
        }
        return Yes(answer with { Basis = "同一接口调用数据的合流" });
    }
    public bool Same(QueryContext c, InterfaceDataName a, InterfaceDataName b) => Compare(c, a, b) is { IsSuccess: true, Value: true };
    internal Outcome<bool?> Compare(QueryContext c, InterfaceDataName a, InterfaceDataName b)
    {
        if (IsPending(a) || IsPending(b)) return Outcome<bool?>.Success(null);
        if (a.Object != b.Object || a.Slot != b.Slot) return Outcome<bool?>.Success(false);
        if (a.Interface == b.Interface) return Outcome<bool?>.Success(true);
        var x = c.Get(names, a.Interface); var y = c.Get(names, b.Interface);
        if (!x.IsSuccess) return x.Propagate<bool?>();
        if (!y.IsSuccess) return y.Propagate<bool?>();
        if (x.Value == NameLattice.Pending || y.Value == NameLattice.Pending) return Outcome<bool?>.Success(null);
        return Outcome<bool?>.Success(x.Value.Name is EntityName { Entity: ClassEntity xc }
            && y.Value.Name is EntityName { Entity: ClassEntity yc } && xc == yc);
    }
    private static void Sum(Term term, List<Term> parts, ref BigInteger constant)
    {
        if (term.Operator is CoreOperator { Operation: CoreOperation.Add }) { foreach (var p in term.Operands) Sum(p, parts, ref constant); }
        else if (term.ConstantValue is { } n) constant += n;
        else parts.Add(term);
    }
    private static Term Add(QueryContext c, Term term, long n) => c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), term.Width, term,
        c.Snapshot.Terms.Constant(new BigInteger(n) & ((BigInteger.One << term.Width)-1), term.Width));
    private static Term Address(QueryContext c, Location l) => l.Offset is { } offset ? Add(c, l.Root, checked((long)offset)) : l.UnknownOffsetAddress ?? l.Root;
    private static Outcome<InterfaceDataName> Yes(InterfaceDataName name) => Outcome<InterfaceDataName>.Success(name);
    private static Outcome<InterfaceDataName> No(string code, string detail, Reason? cause = null) => Outcome<InterfaceDataName>.Failure(new("dispatch.interface-"+code, detail, cause));
}

/// <summary>接口调用数据的身份为对象、接口和槽；尚缺命名依据时保留底值。</summary>
internal sealed class InterfaceDataLattice(Term value) : ILattice<InterfaceDataName>
{
    public InterfaceDataName Bottom { get; } = InterfaceDataQuery.Pending(value);
    private static bool Same(InterfaceDataName a, InterfaceDataName b) => a.Object == b.Object && a.Interface == b.Interface && a.Slot == b.Slot;
    public InterfaceDataName Join(InterfaceDataName a, InterfaceDataName b) => InterfaceDataQuery.IsPending(a) ? b
        : InterfaceDataQuery.IsPending(b) || Same(a, b) ? a : throw new InvalidOperationException("接口调用数据的身份不一致。");
    public bool LessOrEqual(InterfaceDataName a, InterfaceDataName b) => InterfaceDataQuery.IsPending(a) || Same(a, b);
}
