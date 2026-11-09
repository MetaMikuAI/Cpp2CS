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
                // 重叠只接受整段复制（clang 用两次重叠的宽写入复制不是 16 字节倍数的结构体）：重叠的字节两次写入同一个值。
                // 先清零再写部分字段这类重叠是两次不同的写入，不合并。
                if (members.Any(m => m.Offset < end && target.Offset < m.Offset + m.Value.Width / 8
                    && (crossedReads.Count > 0 || !SameBytes(m.Value, m.Offset, operands[1], target.Offset)))) break;
                members.Add((store, operands[0], operands[1], target.Offset));
                if (members.Count < 2) continue;
                var start = members.Min(m => m.Offset);
                var width = (int)(members.Max(m => m.Offset + m.Value.Width / 8) - start) * 8;
                if (Covering(members, start, width) is not { } pieces) continue;
                var first = members.First(m => m.Offset == start);
                var value = values.Syms.Concat(pieces);
                if ((Locate(first.Address, width) ?? (TypeOf(value) is { } valueType && types.Size(valueType) * 8 == width ? PointerElement(first.Address, valueType) : null)
                    ?? (BufferElement(first.Address) is { } bufferType && types.Size(bufferType) * 8 == width ? PointerElement(first.Address, bufferType) : null))
                    is not { Type: { } type } location
                    || types.Kind(type) != TypeKind.Struct || types.Size(type) * 8 != width) continue;
                if (crossedReads.Count > 0 && (location.Kind is not (LocationKind.Instance or LocationKind.Reference)
                    || crossedReads.Any(r => AccessAddress(r.Address).Offset < start + width / 8
                        && start < AccessAddress(r.Address).Offset + r.Width / 8))) continue;
                found = new StoreGroup(members.Select(m => m.Store).ToArray(), location, value);
            }
            found ??= RegionGroup(statements, i, result);
            if (found is not null)
                foreach (var member in found.Members) result[member] = found;
        }
        return result;
    }

    /// <summary>
    /// clang 拆开结构体局部（SROA）后写回对象字段：各叶子的写入和同一对象其他字段的写入交错，填充字节不再写入。
    /// 领头写入落在含不可访问叶子的值类型字段内时，由外向内取这样的字段：从领头写入起、到第一个读取、调用或别的根的写入为止，
    /// 同根且落在该字段内的写入盖满它的全部叶子（填充不计），同根的其余写入都和它不相交，就合成一次整体写入，填充为未定义。
    /// 这些写入互不相交、之间没有读取，提前到第一个成员处不改变结果；第一个成员已验证接收者。
    /// </summary>
    private StoreGroup? RegionGroup(IReadOnlyList<Stmt> statements, int i, Dictionary<Store, StoreGroup> result)
    {
        var leader = (Store)statements[i];
        var operands = values.Operands(leader);
        var origin = AccessAddress(operands[0]);
        if (origin.Index is not null || operands[1].Width % 8 != 0 || Locate(operands[0], operands[1].Width) is not { Path.Count: > 1 } leaf) return null;
        for (var k = 1; k < leaf.Path.Count; k++)
        {
            var field = leaf.Path[k - 1];
            if (field.DeclaringType is not DefinitionRef owner || field.Field.Type.Substitute(owner.Arguments, []) is not DefinitionRef structure
                || types.Kind(structure) != TypeKind.Struct || types.Size(structure) is not (> 0 and var size)
                || types.Project(structure, leaf.Path.Skip(k).ToArray()) is not { Bit: var bit } || bit % 8 != 0) continue;
            var leaves = types.Projections(structure).ToArray();
            if (!leaves.Any(l => l.Path.Any(f => !ManagedAccess.Field(types, method, f, f.DeclaringType)))) continue;
            var start = origin.Offset - bit / 8;
            var end = start + size;
            var members = new List<(Store Store, Sym Address, Sym Value, long Offset)>();
            for (var j = i; j < statements.Count; j++)
            {
                var statement = statements[j];
                if (values.ReadsAt(statement).Count > 0) break;
                if (statement is Define or Nop or Call { Op.Kind: OpKind.WriteBarrier }) continue;
                if (statement is not Store store) break;
                var storeOperands = values.Operands(store);
                var target = AccessAddress(storeOperands[0]);
                if (target with { Offset = origin.Offset } != origin || storeOperands[1].Width % 8 != 0) break;
                var to = target.Offset + storeOperands[1].Width / 8;
                if (to <= start || target.Offset >= end) continue;
                if (target.Offset < start || to > end || result.ContainsKey(store)
                    || members.Any(m => m.Offset < to && target.Offset < m.Offset + m.Value.Width / 8 && !SameBytes(m.Value, m.Offset, storeOperands[1], target.Offset))) break;
                members.Add((store, storeOperands[0], storeOperands[1], target.Offset));
            }
            bool Padding(long at) => !leaves.Any(l => l.Bit / 8 <= at - start && at - start < (l.Bit + l.Width + 7) / 8);
            if (members.Count == 0 || members.FirstOrDefault(m => m.Offset == start) is not { Store: not null } first
                || Covering(members, start, size * 8, Padding) is not { } pieces
                || Locate(first.Address, size * 8) is not { } location || !location.Type.Equals(structure)) continue;
            return new StoreGroup(members.Select(m => m.Store).ToArray(), location, values.Syms.Concat(pieces));
        }
        return null;
    }

    /// <summary>
    /// store 所在的清零序列：同一块中相邻、与它同根且无下标、值为零的写入，之间只有不读内存的定义、空语句与写屏障。
    /// 按语句次序给出各写入的地址与相对根的字节区间；store 不是这样的写入时为 null。clang 用几次宽写入清零相邻字段，单次写入可能跨过值类型字段的边界。
    /// </summary>
    public IReadOnlyList<(Store Store, Sym Address, long Start, long End)>? ZeroRun(Store store)
    {
        static bool Zero(Sym value) => SymTable.Resolve(value) switch { ConstSym { Value: 0 } => true, ConcatSym concat => concat.Parts.All(Zero), _ => false };
        var operands = values.Operands(store);
        var origin = AccessAddress(operands[0]);
        if (origin.Index is not null || operands[1].Width % 8 != 0 || !Zero(operands[1])) return null;
        bool Member(Stmt statement) => statement is Store other && values.Operands(other) is var o && o[1].Width % 8 == 0 && Zero(o[1])
            && AccessAddress(o[0]) with { Offset = origin.Offset } == origin;
        bool Passable(Stmt statement) => values.ReadsAt(statement).Count == 0 && statement is Define or Nop or Call { Op.Kind: OpKind.WriteBarrier };
        var statements = values.BlockOf(store).Statements;
        var index = -1;
        for (var k = 0; k < statements.Count; k++)
            if (ReferenceEquals(statements[k], store)) index = k;
        var (first, last) = (index, index);
        for (var j = index - 1; j >= 0 && (Passable(statements[j]) || Member(statements[j]) && values.ReadsAt(statements[j]).Count == 0); j--)
            if (statements[j] is Store) first = j;
        for (var j = index + 1; j < statements.Count && (Passable(statements[j]) || Member(statements[j]) && values.ReadsAt(statements[j]).Count == 0); j++)
            if (statements[j] is Store) last = j;
        var run = new List<(Store, Sym, long, long)>();
        for (var j = first; j <= last; j++)
            if (statements[j] is Store member)
            {
                var o = values.Operands(member);
                var start = AccessAddress(o[0]).Offset;
                run.Add((member, o[0], start, start + o[1].Width / 8));
            }
        return run;
    }

    /// <summary>两次写入重叠的字节是否是同一个值。</summary>
    private bool SameBytes(Sym first, long firstOffset, Sym second, long secondOffset)
    {
        var from = Math.Max(firstOffset, secondOffset);
        var to = Math.Min(firstOffset + first.Width / 8, secondOffset + second.Width / 8);
        return ReferenceEquals(SymTable.Resolve(values.Syms.Slice(first, (int)(from - firstOffset) * 8, (int)(to - from) * 8)),
            SymTable.Resolve(values.Syms.Slice(second, (int)(from - secondOffset) * 8, (int)(to - from) * 8)));
    }

    /// <summary>
    /// 写入组从低到高的各段：每个字节取语句次序上最后一次写入它的成员（重叠处两次写入的值相同），相邻且来自同一成员的字节合成一段。
    /// 没有被写入的字节是填充时为未定义，否则为 null。
    /// </summary>
    private List<Sym>? Covering(List<(Store Store, Sym Address, Sym Value, long Offset)> members, long start, int width, Func<long, bool>? padding = null)
    {
        const int Undefined = -1;
        var pieces = new List<Sym>();
        int? owner = null;
        var from = 0L;
        for (var at = start; at <= start + width / 8; at++)
        {
            int? current = null;
            if (at < start + width / 8)
            {
                for (var k = members.Count - 1; k >= 0 && current is null; k--)
                    if (members[k].Offset <= at && at < members[k].Offset + members[k].Value.Width / 8) current = k;
                if (current is null && padding?.Invoke(at) == true) current = Undefined;
                if (current is null) return null;
            }
            if (current == owner && at < start + width / 8) continue;
            if (owner is Undefined) pieces.Add(values.Syms.Undef((int)(at - from) * 8));
            else if (owner is { } previous)
            {
                var member = members[previous];
                pieces.Add(values.Syms.Slice(member.Value, (int)(from - member.Offset) * 8, (int)(at - from) * 8));
            }
            owner = current;
            from = at;
        }
        return pieces;
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

    /// <summary>期望的值类型没有自己的定义（类型参数）时，各段来自对同一段内存的读取就是对该位置的整体读取。</summary>
    public ReadSym? OpenWholeRead(ConcatSym bits, TypeRef? expected) =>
        expected is not null and not DefinitionRef && types.Kind(expected) == TypeKind.Struct ? WholeRead(bits, expected) : null;

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
            if (width <= 0 || offset * 8 + width > bits.Width || !FromReads(bits, offset, width, ref address, reads)) return null;
        return Snapshot(address, reads, structure, total);
    }

    /// <summary>位段 [offset, offset + width)（字节偏移、位宽）的各片都读自同段内存时，记下这些读取并给出或核对整体的起点。</summary>
    private bool FromReads(Sym bits, int offset, int width, ref Sym? address, HashSet<ReadSym> reads)
    {
        var part = SymTable.Resolve(values.Syms.Slice(bits, offset * 8, width));
        var pieceOffset = offset;
        foreach (var piece in part is ConcatSym concat ? concat.Parts : [part])
        {
            var (source, low) = piece is SliceSym slice ? (SymTable.Resolve(slice.Base), slice.Low) : (SymTable.Resolve(piece), 0);
            if (source is not ReadSym read || low % 8 != 0 || piece.Width % 8 != 0) return false;
            var start = values.Syms.Binary(BinOp.Add, read.Address, values.Syms.Const(unchecked((ulong)(low / 8 - pieceOffset)), 64), 64);
            if (address is not null && Decompose(address) != Decompose(start)) return false;
            address = start;
            reads.Add(read);
            pieceOffset += piece.Width / 8;
        }
        return true;
    }

    /// <summary>
    /// var s = p.S; s.F = v; p.S = s 拆开后写回的值：一部分直接字段原样来自同一结构体位置的读取，其余是新值，原样的字段里有不可访问的叶子。
    /// 在这些读取的第一处整体读取该位置（快照），再改写其余直接字段；快照多读的字节属于同一位置，提前读取不改变异常。
    /// 位置由读自该结构体类型位置的字段定下；改写的字段照常按字段访问（不可访问的经访问器）。
    /// 没有这样的读取时，原样的字段可以是同一个结构体值（如构造函数写出的局部）在相同位置的片，快照就是这个值。
    /// </summary>
    public (Sym Snapshot, IReadOnlyList<ProjectedSym> Changed)? UpdatedRead(Sym bits, DefinitionRef structure)
    {
        var total = types.Size(structure) * 8;
        if (total <= 0 || total > bits.Width || FieldValues(bits, structure) is not { } direct) return null;
        var groups = types.Leaves(structure).GroupBy(l => l.Path[0]).ToArray();
        bool Hidden(IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> leaves) =>
            leaves.Any(l => l.Path.Any(f => !ManagedAccess.Field(types, method, f, f.DeclaringType)));
        bool Kept(IEnumerable<(IReadOnlyList<FieldRef> Path, TypeRef Type, int Offset)> leaves, ref Sym? at, HashSet<ReadSym> found)
        {
            foreach (var leaf in leaves)
                if (StorageBits(leaf.Type) is not (> 0 and var width) || leaf.Offset * 8 + width > bits.Width || !FromReads(bits, leaf.Offset, width, ref at, found)) return false;
            return true;
        }
        Sym? address = null;
        foreach (var group in groups)
        {
            Sym? start = null;
            if (Kept(group, ref start, []) && start is not null && Locate(start, total) is { } located && located.Type.Equals(structure))
            {
                address = start;
                break;
            }
        }
        Sym? whole = null;
        if (address is null)
            foreach (var group in groups)
            {
                Sym? candidate = null;
                if (group.All(l => StorageBits(l.Type) is > 0 and var width && l.Offset * 8 + width <= bits.Width && FromValue(bits, l.Offset, width, total, ref candidate))
                    && candidate is not null && TypeOf(candidate) is { } type && type.Equals(structure))
                {
                    whole = candidate;
                    break;
                }
            }
        if (address is null && whole is null) return null;
        var reads = new HashSet<ReadSym>();
        var changed = new List<ProjectedSym>();
        var hiddenKept = false;
        foreach (var group in groups)
        {
            var at = address;
            var same = whole;
            var found = new HashSet<ReadSym>();
            if (address is not null ? Kept(group, ref at, found)
                : group.All(l => StorageBits(l.Type) is > 0 and var width && l.Offset * 8 + width <= bits.Width && FromValue(bits, l.Offset, width, total, ref same)))
            {
                reads.UnionWith(found);
                hiddenKept |= Hidden(group);
                continue;
            }
            if (direct.FirstOrDefault(d => d.Projection.Path is [var field] && field.Equals(group.Key)) is not { } own) return null;
            changed.Add(own);
        }
        if (!hiddenKept || changed.Count == 0) return null;
        if (whole is not null) return (whole, changed);
        return Snapshot(address, reads, structure, total) is { } snapshot ? (snapshot, changed) : null;
    }

    /// <summary>位段 [offset, offset + width)（字节偏移、位宽）的各片都是同一个整体值 whole 在相同位置的片；whole 的位宽为 total。</summary>
    private bool FromValue(Sym bits, int offset, int width, int total, ref Sym? whole)
    {
        var part = SymTable.Resolve(values.Syms.Slice(bits, offset * 8, width));
        var at = offset * 8;
        foreach (var piece in part is ConcatSym concat ? concat.Parts : [part])
        {
            var (source, low) = piece is SliceSym slice ? (SymTable.Resolve(slice.Base), slice.Low) : (SymTable.Resolve(piece), 0);
            if (source.Width != total || low != at || source is ConcatSym or ConstSym or UndefSym || whole is not null && !Equals(whole, source)) return false;
            whole = source;
            at += piece.Width;
        }
        return true;
    }

    /// <summary>在这些读取的第一处对 address 处结构体位置的整体读取；各读取之间只能是定义。</summary>
    private ReadSym? Snapshot(Sym? address, HashSet<ReadSym> reads, TypeRef structure, int total)
    {
        if (address is null || (Locate(address, total) is { } located && located.Type.Equals(structure) ? located : PointerElement(address, structure)) is null) return null;
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
