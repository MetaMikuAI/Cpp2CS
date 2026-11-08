using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Control;
using Cpp2CS.Recovery.Memory;
using Cpp2CS.Recovery.Runtime;
using Cpp2CS.Recovery.Typing;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Lowering;

/// <summary>机器语句的下降：读写、分支、跳转表、返回。</summary>
internal sealed partial class BodyBuilder
{
    private Terminator? Lower(Block block, int index, List<ManagedStatement> output)
    {
        var statement = block.Statements[index];
        var operands = values.Operands(statement);
        // 地址选择分发成条件读取时，只能快照整个选择，不能提前读取未选中的字段。
        if (statement is Define && operands is [OpSym { Op.Kind: OperatorKind.Select } selection]
            && Reads(statement).Any(materialized.Contains))
        {
            var selected = View(selection, oracle.TypeOf(selection), statement.Address);
            output.Add(new ManagedAssignment(statement.Address, Local(selection, selected.Type), selected));
            return null;
        }
        foreach (var read in Reads(statement).Concat(oracle.WholeReadsAt(statement)).Where(materialized.Contains))
        {
            // 相邻字段合并的读取逐字段落成局部，以该段的切片为键。
            if (oracle.Parts(read) is { } leaves)
            {
                foreach (var part in leaves)
                    output.Add(new ManagedAssignment(statement.Address, Local(values.Syms.Slice(read, part.Bit, part.Width), part.Leaf.Type), LocationValue(part.Leaf, statement.Address)));
                continue;
            }
            if (Read(read, statement.Address) is { } value)
            {
                var assignment = new ManagedAssignment(statement.Address, Local(read, value.Type), value);
                output.Add(assignment);
                // 只可能抛空引用，而且随后第一次访问同一对象时抛同样的异常：结果没人读就不用写。
                if (value is ArrayLengthValue or StringLengthValue or FieldValue { Accessor: null, Pending: null }
                    && effects.Absorbed(block, index + 1, oracle.Decompose(read.Address).Root, null)) omissibleReads.Add(assignment);
            }
        }
        switch (statement)
        {
            case Define or Phi or Nop or Assign:
                return null;
            case Store store:
                {
                    // 写入组在第一个成员处写出整体值，其余成员不再单独写出。
                    if (oracle.StoreGroupOf(store) is { } group)
                    {
                        if (!ReferenceEquals(group.Members[0], store)) return null;
                        StoreTo(StoreLocation(group.Target, group.Value), group.Value, store.Address, output);
                        return null;
                    }
                    // 清零序列盖满的值类型字段：第一个触及它的写入整体写 default，其余写入里落在它里面的部分不再写。
                    var zeroed = ZeroPlan(store);
                    var own = zeroed.Count > 0 ? oracle.ZeroRun(store)!.First(m => ReferenceEquals(m.Store, store)) : default;
                    bool Planned(long from, long to, ulong address)
                    {
                        if (zeroed.FirstOrDefault(z => z.Start <= from && to <= z.End) is not { Place: not null } entry) return false;
                        if (ReferenceEquals(entry.Emitter, store) && emittedZeros.Add(entry.Place))
                            StoreTo(entry.Place, values.Syms.Zero((int)(entry.End - entry.Start) * 8), address, output);
                        return true;
                    }
                    var location = oracle.Locate(operands[0], store.Value.Width) ?? oracle.ViewLocate(operands[0], store.Value.Width, store);
                    if (location is not null && zeroed.Count > 0 && Planned(own.Start, own.End, store.Address)) return null;
                    if (location is not null) location = StoreLocation(location, operands[1]);
                    if (location is null && oracle.Split(operands[0], store.Value.Width) is { } leaves)
                    {
                        // 跨字段的写入按布局拆为逐字段写入（寄存器对、合并的清零等一次写入多个字段）；
                        // 只覆盖字段一部分的段写为读改写：f = (f & ~掩码) | (段 << 位移)，浮点字段在同宽整数的位型上改写。
                        var wholeEnd = 0;
                        foreach (var part in leaves)
                        {
                            if (part.Bit < wholeEnd) continue;
                            if (zeroed.Count > 0 && Planned(own.Start + part.Bit / 8, own.Start + (part.Bit + part.Width + 7) / 8, store.Address)) continue;
                            if (WholeStruct(part, store.Value.Width) is var (place, bit, size))
                            {
                                StoreTo(place, values.Syms.Slice(operands[1], bit, size), store.Address, output);
                                wholeEnd = bit + size;
                                continue;
                            }
                            var leaf = part.Leaf;
                            var leafTarget = LocationValue(leaf, store.Address, store: true);
                            var slice = values.Syms.Slice(operands[1], part.Bit, part.Width);
                            var width = Width(leaf.Type);
                            var mask = Expr.Mask(part.Width) << part.FieldBit;
                            ManagedValue Merged(ManagedValue current, ManagedValue bits, TypeRef type)
                            {
                                ManagedValue shifted = part.FieldBit == 0 ? bits : new BinaryValue(BinOp.Shl, bits, new ConstantValue((ulong)part.FieldBit, types.Int32, 32), type, width);
                                var kept = new BinaryValue(BinOp.And, current, new ConstantValue(~mask & Expr.Mask(width), type, width), type, width);
                                return new BinaryValue(BinOp.Or, kept, shifted, type, width);
                            }
                            var carrier = types.Kind(leaf.Type) is TypeKind.Float or TypeKind.Double ? types.Integer(width, signed: false) : leaf.Type;
                            ManagedValue leafValue;
                            if (part.FieldBit == 0 && part.Width == (ManagedTypes.IsReferenceType(leaf.Type) ? 64 : types.Size(leaf.Type) * 8))
                                leafValue = View(slice, leaf.Type, store.Address);
                            else if (types.Kind(leaf.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double && IntegerBits(slice, carrier, store.Address) is { } bits)
                            {
                                if (bits is ConstantValue constant && KnownConstant(output, leafTarget) is { } known)
                                {
                                    // 字段刚写过常量，中间没有别的写入：按位合并出新常量；值不变时这次写入不改变任何状态。
                                    var merged = known.Bits & ~mask | (constant.Bits & Expr.Mask(part.Width)) << part.FieldBit;
                                    if ((merged & Expr.Mask(width)) == (known.Bits & Expr.Mask(width))) continue;
                                    leafValue = known with { Bits = merged & Expr.Mask(width) };
                                }
                                else if (carrier == leaf.Type)
                                    leafValue = Merged(LocationValue(leaf, store.Address), bits, leaf.Type);
                                else
                                    leafValue = new ConversionValue(ConvKind.Bitcast,
                                        Merged(new ConversionValue(ConvKind.Bitcast, LocationValue(leaf, store.Address), carrier, width), bits, carrier), leaf.Type, width);
                            }
                            else
                                leafValue = Hole(store.Address, $"内存 字段 {leaf.Type} 的部分写入", leaf.Type);
                            output.Add(leafTarget is LocalValue leafLocal ? new ManagedAssignment(store.Address, leafLocal, leafValue) : new ManagedStore(store.Address, leafTarget, leafValue));
                        }
                        return null;
                    }
                    if (location is null) { output.Add(new ManagedHole(store.Address, $"内存 写入位置 {operands[0]}", false)); holes.Add(new(store.Address, $"内存 写入位置 {operands[0]}")); return null; }
                    StoreTo(location, operands[1], store.Address, output);
                    return null;
                }
            case Call call:
                return LowerCall(block, index, call, operands, output);
            case Ir.Branch branch:
                return new Branch(branch.Address, View(operands[0], types.Boolean, branch.Address), branch.Target, branch.Fallthrough);
            case Ir.Jump jump:
                return new Jump(jump.Address, jump.Target);
            case Return ret:
                return new Statement(new ManagedReturn(ret.Address, ReturnValue(ret, operands)));
            case Trap trap:
                return Fail(trap.Address, $"控制 陷入 {trap.Kind}", terminal: true);
            case IndirectJump { Targets.Length: > 0 } jump when oracle.TableIndex(operands[0]) is { } tableIndex:
                return new Switch(jump.Address, View(tableIndex, types.Int32, jump.Address), jump.Targets);
            case IndirectJump jump:
                return Fail(jump.Address, "控制 间接跳转的目标集合或下标未知", terminal: true);
            default:
                return Fail(statement.Address, $"语句 {statement.GetType().Name}", terminal: false) is Statement s ? AddHole(output, s) : null;
        }
    }

    /// <summary>
    /// 段所在的值类型字段整个落在这次写入内、且含不可访问的叶子时，按整个字段写入（合并的清零跨过几个 Nullable 字段）：
    /// 两种写法写的是同一段字节，整体写入不需要访问私有叶子。取最外层整个落在写入内的值类型字段。
    /// </summary>
    private (Location Place, int Bit, int Width)? WholeStruct(AccessPart part, int width)
    {
        var path = part.Leaf.Path;
        for (var i = 1; i < path.Count; i++)
        {
            if (FieldType(path[i - 1], null) is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct) continue;
            var inner = types.Projections(structure).ToArray();
            if (inner.Length == 0 || inner.Any(p => !p.Fits(types.StorageBits(structure)))) return null;
            var suffix = path.Skip(i).ToArray();
            if (inner.FirstOrDefault(p => p.Path.SequenceEqual(suffix)) is not { } leaf) return null;
            var bit = part.Bit - part.FieldBit - leaf.Bit;
            var size = types.Size(structure) * 8;
            if (size <= 0 || bit < 0 || bit + size > width) continue;
            if (!inner.Any(p => p.Path.Any(f => !fields.Accessible(f, f.DeclaringType)))) return null;
            return (part.Leaf with { Path = path.Take(i).ToArray(), Type = structure }, bit, size);
        }
        return null;
    }

    /// <summary>
    /// 清零序列（<see cref="TypeOracle.ZeroRun"/>）盖满的值类型字段：取各写入拆出的叶子所在的最外层、含不可访问叶子的值类型字段，
    /// 序列的字节区间盖满它时整体写 default，写在序列中第一个触及它的写入处。序列都是零、之间没有读取，提前写零不改变结果，也不需要访问私有叶子。
    /// 区间相对序列的根，序列中各写入共用同一份计划。
    /// </summary>
    private List<(Location? Place, long Start, long End, Store? Emitter)> ZeroPlan(Store store)
    {
        if (zeroPlans.TryGetValue(store, out var known)) return known;
        var plan = new List<(Location? Place, long Start, long End, Store? Emitter)>();
        if (oracle.ZeroRun(store) is { Count: > 1 } run)
        {
            bool Covered(long start, long end)
            {
                var at = start;
                foreach (var (_, _, from, to) in run.OrderBy(m => m.Start))
                    if (from <= at && to > at) at = to;
                return at >= end;
            }
            foreach (var (member, address, offset, _) in run)
                foreach (var part in oracle.Split(address, values.Operands(member)[1].Width) ?? [])
                {
                    var path = part.Leaf.Path;
                    for (var i = 1; i < path.Count; i++)
                    {
                        if (FieldType(path[i - 1], null) is not DefinitionRef structure || types.Kind(structure) != TypeKind.Struct) continue;
                        var inner = types.Projections(structure).ToArray();
                        var suffix = path.Skip(i).ToArray();
                        if (inner.Length == 0 || inner.FirstOrDefault(p => p.Path.SequenceEqual(suffix)) is not { } leaf) break;
                        if (!inner.Any(p => p.Path.Any(f => !fields.Accessible(f, f.DeclaringType)))) break;
                        var bit = part.Bit - part.FieldBit - leaf.Bit;
                        if (bit % 8 != 0) break;
                        var start = offset + bit / 8;
                        var end = start + types.Size(structure);
                        if (plan.Any(z => z.Start == start && z.End == end)) break;
                        if (!Covered(start, end)) continue;
                        // 触及它的写入要么整个落在里面，要么按字段拆开写：否则那次写入按定位整体写出，跳不过这一段。
                        if (run.Any(m => m.Start < end && start < m.End && !(start <= m.Start && m.End <= end)
                            && (oracle.Locate(m.Address, (int)(m.End - m.Start) * 8) ?? oracle.ViewLocate(m.Address, (int)(m.End - m.Start) * 8, m.Store)) is not null)) break;
                        var emitter = run.First(m => m.Start < end && start < m.End).Store;
                        plan.Add((part.Leaf with { Path = path.Take(i).ToArray(), Type = structure }, start, end, emitter));
                        break;
                    }
                }
            // 计划之间不能相交：相交说明同一段字节有两种解释。
            if (plan.Any(a => plan.Any(b => !ReferenceEquals(a.Place, b.Place) && a.Start < b.End && b.Start < a.End))) plan.Clear();
            foreach (var (member, _, _, _) in run) zeroPlans[member] = plan;
        }
        zeroPlans[store] = plan;
        return plan;
    }

    /// <summary>
    /// 本块里 <paramref name="target"/> 最近一次写入的常量。其后只能是对其他字段的常量写入（合并的清零序列）：
    /// 字段不同就不会是同一位置；同一字段经别的接收者写入可能是别名，其余语句可能改写它，都不算已知。
    /// </summary>
    private static ConstantValue? KnownConstant(List<ManagedStatement> output, ManagedValue target)
    {
        var field = target switch { FieldValue f => f.Field, StaticFieldValue s => s.Field, _ => null };
        if (field is null) return null;
        for (var i = output.Count - 1; i >= 0; i--)
            switch (output[i])
            {
                case ManagedStore { Target: var written, Value: ConstantValue value } when written.Equals(target):
                    return value;
                case ManagedStore { Target: var written, Value: ConstantValue } when written switch { FieldValue f => f.Field, StaticFieldValue s => s.Field, _ => null } is { } other && !other.Equals(field):
                    continue;
                default:
                    return null;
            }
        return null;
    }

    private static Terminator? AddHole(List<ManagedStatement> output, Statement hole)
    {
        output.Add(hole.Value);
        return null;
    }

    private IReadOnlyList<ReadSym> Reads(Stmt statement) => values.ReadsAt(statement);

    /// <summary>
    /// 对位置的整体写入。值不能整体写出时（见 <see cref="Leafwise"/>）逐个字段写入对应的位段，
    /// 每个字段再按同一规则整体写入或继续分解，因而值类型字段可经其访问器整体写入。
    /// </summary>
    private void StoreTo(Location place, Sym bits, ulong address, List<ManagedStatement> output)
    {
        if (Leafwise(bits, place.Type) && oracle.FieldValues(bits, (DefinitionRef)place.Type) is { } fields)
        {
            foreach (var (projection, part) in fields)
                StoreTo(place with { Path = [.. place.Path, .. projection.Path], Type = projection.Type }, part, address, output);
            return;
        }
        if (StoreThroughProperty(place, bits, address, output)) return;
        var destination = LocationValue(place, address, store: true);
        var value = View(bits, place.Type, address);
        output.Add(destination is LocalValue local ? new ManagedAssignment(address, local, value) : new ManagedStore(address, destination, value));
    }

    /// <summary>
    /// 写入经过不可访问的值类型字段，而该字段有证明过的 getter 和 setter 时，是 var t = o.P; t.f = v; o.P = t 内联后只留下的那次写入：
    /// 取值和写回都只访问这个字段，其余叶子写回原值，与只写一个叶子不可区分。
    /// </summary>
    private bool StoreThroughProperty(Location place, Sym bits, ulong address, List<ManagedStatement> output)
    {
        for (var i = 0; i + 1 < place.Path.Count; i++)
        {
            var type = FieldType(place.Path[i], null);
            var holder = place with { Path = place.Path.Take(i + 1).ToArray(), Type = type };
            if (LocationValue(holder, address) is not FieldValue { Pending: not null } read) continue;
            if (LocationValue(holder, address, store: true) is not FieldValue { Pending: not null } written
                || templates.Accessor(read.Field, type, false, read.Receiver.Type) is null
                || templates.Accessor(written.Field, type, true, written.Receiver.Type) is null) return false;
            var copy = NewLocal(type);
            output.Add(new ManagedAssignment(address, copy, read));
            var leaf = Nest(new AddressValue(copy), place.Path.Skip(i + 1).ToArray(), place.Type, true, address);
            output.Add(new ManagedStore(address, leaf, View(bits, place.Type, address)));
            output.Add(new ManagedStore(address, written, copy));
            return true;
        }
        return false;
    }

    /// <summary>表示链上的各层共享地址，写入的层级取值的定义类型；经过的值类型字段须可访问（写入目标以地址给出）。</summary>
    private Location StoreLocation(Location location, Sym value) =>
        oracle.TypeOf(value) is { } source && oracle.Inside(location.Type, source) is var (path, inner)
        && path.Take(types.Kind(inner) == TypeKind.Struct ? path.Count : path.Count - 1).All(f => fields.Accessible(f, f.DeclaringType))
        ? location with { Path = [.. location.Path, .. path], Type = inner } : location;

    private ManagedValue? ReturnValue(Return ret, IReadOnlyList<Sym> operands)
    {
        var type = oracle.ReturnType;
        if (ManagedTypes.IsVoid(type)) return null;
        // 不透明返回值存放在调用者的缓冲区，以局部承接。
        if (analysis.Signature.Return is { Transfer: Transfer.ResultBuffer, Size: < 0 })
            return analysis.Memory.Find(LocalSpace.Result, 0, 1) is { Promoted: false } ? CellLocal((LocalSym)values.Syms.Local(LocalSpace.Result, 0)) : Hole(ret.Address, "返回 不透明返回值未写入", type);
        if (ret.Pieces.Length == 0) return Hole(ret.Address, "返回 返回值缺失", type);
        var width = analysis.Signature.Return is { } r ? MethodEnvironment.ValueWidth(r) : Width(type);
        return View(values.ReturnContent(ret, operands, width), type, ret.Address);
    }
}
