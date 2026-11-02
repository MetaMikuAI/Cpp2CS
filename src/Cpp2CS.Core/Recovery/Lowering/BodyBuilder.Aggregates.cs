using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    private readonly HashSet<Store> aggregateStores = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<(Sym, DefinitionRef), ReadSym> aggregateReads = [];
    private readonly Dictionary<Stmt, List<ReadSym>> aggregateReadSites = new(ReferenceEqualityComparer.Instance);

    /// <summary>同宽的单字段结构体与其字段共享地址，来源类型决定本次写入的层级。</summary>
    private Location StoreLocation(Location location, Sym value) => types.Kind(location.Type) == TypeKind.Struct
        && oracle.TypeOf(value) is { } source && !source.Equals(location.Type)
        && oracle.FieldAt(location.Type, RuntimeLayout.ObjectHeaderSize, value.Width, false, false) is var (path, inner) && inner.Equals(source)
        ? location with { Path = [.. location.Path, .. path], Type = inner } : location;

    /// <summary>结构体的所有叶子来自同段内存的连续读取时，在第一次读取处保存整体值。</summary>
    private ReadSym? AggregateRead(Sym bits, DefinitionRef structure)
    {
        if (aggregateReads.TryGetValue((bits, structure), out var known)) return known;
        Sym? address = null;
        var reads = new HashSet<ReadSym>();
        foreach (var (_, type, offset) in Leaves(structure, 0))
        {
            if (offset * 8 + Width(type) > bits.Width) return null;
            var part = SymTable.Resolve(values.Syms.Slice(bits, offset * 8, Width(type)));
            var (source, low) = part is SliceSym slice ? (slice.Base, slice.Low) : (part, 0);
            if (source is not ReadSym read || low % 8 != 0) return null;
            var start = values.Syms.Binary(BinOp.Add, read.Address, values.Syms.Const(unchecked((ulong)(low / 8 - offset)), 64), 64);
            if (address is not null && oracle.Decompose(address) != oracle.Decompose(start)) return null;
            address = start;
            reads.Add(read);
        }
        var width = types.Size(structure) * 8;
        if (address is null || oracle.Locate(address, width) is not { } location || !location.Type.Equals(structure)) return null;
        var block = order.FirstOrDefault(b => reads.All(r => b.Statements.Any(s => ReferenceEquals(s, r.Site))));
        if (block is null) return null;
        var sites = reads.Select(r => block.Statements.FindIndex(s => ReferenceEquals(s, r.Site))).ToArray();
        var first = sites.Min();
        // 不移动读取跨过写入、调用或不相关的读取，保留原来的异常与副作用顺序。
        for (var i = first; i <= sites.Max(); i++)
            if (block.Statements[i] is not Define || Reads(block.Statements[i]).Any(r => !reads.Contains(r))) return null;
        var site = block.Statements[first];
        var whole = values.Syms.Read(site, -1 - aggregateReads.Count, address, width);
        aggregateReads[(bits, structure)] = whole;
        if (!aggregateReadSites.TryGetValue(site, out var at)) aggregateReadSites[site] = at = [];
        at.Add(whole);
        return whole;
    }

    /// <summary>连续写入完整覆盖同一结构体时，按布局拼回整体赋值；不跨越读取或其他副作用。</summary>
    private (Location Target, Sym Value)? AggregateStore(Block block, int index)
    {
        var first = values.Operands(block.Statements[index]);
        var origin = oracle.Decompose(first[0]);
        var parts = new List<Sym> { first[1] };
        var stores = new List<Store>();
        var width = first[1].Width;
        for (var i = index + 1; i < block.Statements.Count; i++)
        {
            var next = block.Statements[i];
            if (Reads(next).Any()) break;
            if (next is Define or Nop) continue;
            if (next is not Store store || aggregateStores.Contains(store)) break;
            var operands = values.Operands(store);
            var target = oracle.Decompose(operands[0]);
            if (width % 8 != 0 || target != origin with { Offset = origin.Offset + width / 8 }) break;
            parts.Add(operands[1]);
            stores.Add(store);
            width += operands[1].Width;
            if (oracle.Locate(first[0], width) is not { Type: DefinitionRef type } location
                || types.Kind(type) != TypeKind.Struct || types.Size(type) * 8 != width) continue;
            aggregateStores.UnionWith(stores);
            return (location, values.Syms.Concat(parts));
        }
        return null;
    }
}
