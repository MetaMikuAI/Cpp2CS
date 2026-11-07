using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

/// <summary>一组机器写入共同构成的一次 IL 位置写入：成员按语句次序，值为按偏移拼接的各段。</summary>
public sealed record StoreGroup(IReadOnlyList<Store> Members, Location Target, Sym Value);

/// <summary>
/// 位置的整体访问，即 SROA 与读写拆分的逆。clang 把结构体的复制拆成对各段的读写，并可能重排互不重叠的写入；
/// 在未提升的位置（对象字段、元素、经引用、可寻址局部）上，这些段在 IL 中是对同一个结构体位置的一次读写。
/// 写入：同一块中根与下标相同、互不重叠的写入恰好铺满一个结构体位置，之间只有不读内存的定义、空语句与写屏障时，
/// 合成一次对该位置的写入，在第一个成员处写出。
/// 读取：结构体的全部叶子来自同一块中同段内存的读取，之间只有不读其他内存的定义时，在第一次读取处读取整体。
/// 常量写入可越过同一实例内不相交字段的读取；第一次写入已验证接收者，读取不产生新的异常。
/// 其余情况不跨越调用、其他写入或无关读取，原有的异常与副作用次序不变。
/// </summary>
public sealed partial class TypeOracle
{
    /// <summary>各块的写入组；依赖根的类型，求解 φ 后重算。</summary>
    private readonly Dictionary<Block, Dictionary<Store, StoreGroup>> storeGroups = [];
    /// <summary>整体读取按（读取处、地址、宽度）驻留，跨求解保持身份。</summary>
    private readonly Dictionary<(Stmt Site, Sym Address, int Width), ReadSym> wholeReads = new(new WholeReadComparer());
    private readonly Dictionary<Stmt, List<ReadSym>> wholeReadSites = new(ReferenceEqualityComparer.Instance);

    /// <summary>写入所在的写入组；不属于任何组时为 null。</summary>
    public StoreGroup? StoreGroupOf(Store store)
    {
        var block = values.BlockOf(store);
        if (!storeGroups.TryGetValue(block, out var groups)) storeGroups[block] = groups = StoreGroups(block);
        return groups.GetValueOrDefault(store);
    }

    private Dictionary<Store, StoreGroup> StoreGroups(Block block)
    {
        var result = new Dictionary<Store, StoreGroup>(ReferenceEqualityComparer.Instance);
        var statements = block.Statements;
        for (var i = 0; i < statements.Count; i++)
        {
            if (statements[i] is not Store leader || result.ContainsKey(leader)) continue;
            var origin = AccessAddress(values.Operands(leader)[0]);
            var members = new List<(Store Store, Sym Address, Sym Value, long Offset)>();
            var crossedReads = new List<ReadSym>();
            StoreGroup? found = null;
            static bool Constant(Sym value) => value is ConstSym || value is ConcatSym concat && concat.Parts.All(Constant);
            // 成员是语句次序上的前缀；取能铺满结构体位置的最长前缀。
            for (var j = i; j < statements.Count; j++)
            {
                var statement = statements[j];
                var reads = values.ReadsAt(statement);
                if (reads.Count > 0)
                {
                    if (origin.Index is not null || members.Any(m => !Constant(m.Value))
                        || reads.Any(r => AccessAddress(r.Address) with { Offset = origin.Offset } != origin
                            || Locate(r.Address, r.Width) is not { Kind: LocationKind.Instance or LocationKind.Reference })) break;
                    crossedReads.AddRange(reads);
                }
                if (statement is Define or Nop or Call { Op.Kind: OpKind.WriteBarrier }) continue;
                if (statement is not Store store || result.ContainsKey(store)) break;
                var operands = values.Operands(store);
                if (crossedReads.Count > 0 && !Constant(operands[1])) break;
                var target = AccessAddress(operands[0]);
                if (operands[1].Width % 8 != 0 || target with { Offset = origin.Offset } != origin) break;
                var end = target.Offset + operands[1].Width / 8;
                if (members.Any(m => m.Offset < end && target.Offset < m.Offset + m.Value.Width / 8)) break;
                members.Add((store, operands[0], operands[1], target.Offset));
                if (members.Count < 2) continue;
                var ordered = members.OrderBy(m => m.Offset).ToArray();
                var width = ordered.Sum(m => m.Value.Width);
                if ((ordered[^1].Offset - ordered[0].Offset) * 8 + ordered[^1].Value.Width != width) continue;
                if (Locate(ordered[0].Address, width) is not { Type: { } type } location
                    || types.Kind(type) != TypeKind.Struct || types.Size(type) * 8 != width) continue;
                if (crossedReads.Count > 0 && (location.Kind is not (LocationKind.Instance or LocationKind.Reference)
                    || crossedReads.Any(r => AccessAddress(r.Address).Offset < ordered[0].Offset + width / 8
                        && ordered[0].Offset < AccessAddress(r.Address).Offset + r.Width / 8))) continue;
                found = new StoreGroup(members.Select(m => m.Store).ToArray(), location, values.Syms.Concat(ordered.Select(m => m.Value)));
            }
            if (found is not null)
                foreach (var member in found.Members) result[member] = found;
        }
        return result;
    }

    /// <summary>拼接中的读取指向完整结构体位置时，以整体读取证明其定义类型。</summary>
    public ReadSym? CompositeRead(ConcatSym bits)
    {
        var at = 0;
        foreach (var part in bits.Parts)
        {
            var (source, low) = part is SliceSym slice ? (SymTable.Resolve(slice.Base), slice.Low) : (SymTable.Resolve(part), 0);
            if (source is ReadSym read && (low - at) % 8 == 0)
            {
                var address = values.Syms.Binary(BinOp.Add, read.Address, values.Syms.Const(unchecked((ulong)((low - at) / 8)), 64), 64);
                if (Locate(address, bits.Width) is { Type: var structure } && types.Kind(structure) == TypeKind.Struct
                    && types.Size(structure) * 8 == bits.Width && WholeRead(bits, structure) is { } whole) return whole;
            }
            at += part.Width;
        }
        return null;
    }

    /// <summary>结构体值 bits 的全部叶子来自同段内存的读取时，在第一次读取处对该结构体位置的整体读取；不成立时为 null。</summary>
    public ReadSym? WholeRead(Sym bits, TypeRef structure)
    {
        var total = types.Size(structure) * 8;
        if (total <= 0) return null;
        Sym? address = null;
        var reads = new HashSet<ReadSym>();
        // 开放值类型只证明整段复制，不借用原生实例的字段解释 T。
        var ranges = structure is DefinitionRef definition
            ? types.Leaves(definition).Select(l => (l.Offset, Width: StorageBits(l.Type)))
            : [(Offset: 0, Width: total)];
        foreach (var (offset, width) in ranges)
        {
            if (width <= 0 || offset * 8 + width > bits.Width) return null;
            var part = SymTable.Resolve(values.Syms.Slice(bits, offset * 8, width));
            var pieceOffset = offset;
            foreach (var piece in part is ConcatSym concat ? concat.Parts : [part])
            {
                var (source, low) = piece is SliceSym slice ? (SymTable.Resolve(slice.Base), slice.Low) : (SymTable.Resolve(piece), 0);
                if (source is not ReadSym read || low % 8 != 0 || piece.Width % 8 != 0) return null;
                var start = values.Syms.Binary(BinOp.Add, read.Address, values.Syms.Const(unchecked((ulong)(low / 8 - pieceOffset)), 64), 64);
                if (address is not null && Decompose(address) != Decompose(start)) return null;
                address = start;
                reads.Add(read);
                pieceOffset += piece.Width / 8;
            }
        }
        if (address is null || Locate(address, total) is not { } location || !location.Type.Equals(structure)) return null;
        var block = values.BlockOf(reads.First().Site);
        var sites = reads.Select(r => block.Statements.FindIndex(s => ReferenceEquals(s, r.Site))).ToArray();
        if (sites.Any(s => s < 0)) return null;
        var first = sites.Min();
        // 各段之间只能是定义：其中对别处的读取不改内存；整体读取落在第一段处，后面的段读同一对象，提前读不改变异常。
        for (var i = first; i <= sites.Max(); i++)
            if (block.Statements[i] is not Define) return null;
        var site = block.Statements[first];
        if (wholeReads.TryGetValue((site, address, total), out var whole)) return whole;
        whole = values.Syms.Read(site, -1 - wholeReads.Count, address, total);
        wholeReads[(site, address, total)] = whole;
        if (!wholeReadSites.TryGetValue(site, out var at)) wholeReadSites[site] = at = [];
        at.Add(whole);
        return whole;
    }

    /// <summary>以该语句为读取处的整体读取。</summary>
    public IReadOnlyList<ReadSym> WholeReadsAt(Stmt statement) => wholeReadSites.GetValueOrDefault(statement) ?? [];

    /// <summary>值在机器上的存储位宽。</summary>
    public int StorageBits(TypeRef type) => types.StorageBits(type);

    /// <summary>标量叶子的机器位宽。</summary>
    public int LeafBits(TypeRef type) => ManagedTypes.IsReferenceType(type) || type is ByRefRef or PointerRef ? 64 : Math.Max(1, types.Bits(type));

    /// <summary>访问地址的根、偏移与下标；局部地址以所在空间的起点为根，使同一单元内的访问可比较。</summary>
    private (Sym Root, long Offset, Sym? Index, int Scale) AccessAddress(Sym address)
    {
        var location = Decompose(address);
        return location.Root is LocalSym local
            ? location with { Root = values.Syms.Local(local.Space, 0), Offset = location.Offset + local.Offset } : location;
    }

    private sealed class WholeReadComparer : IEqualityComparer<(Stmt Site, Sym Address, int Width)>
    {
        public bool Equals((Stmt Site, Sym Address, int Width) x, (Stmt Site, Sym Address, int Width) y) =>
            ReferenceEquals(x.Site, y.Site) && ReferenceEquals(x.Address, y.Address) && x.Width == y.Width;
        public int GetHashCode((Stmt Site, Sym Address, int Width) key) =>
            HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Site), key.Address.Id, key.Width);
    }
}
