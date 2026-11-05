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
                output.Add(new ManagedAssignment(statement.Address, Local(read, value.Type), value));
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
                    var location = oracle.Locate(operands[0], store.Value.Width);
                    if (location is not null) location = StoreLocation(location, operands[1]);
                    if (location is null && oracle.Split(operands[0], store.Value.Width) is { } leaves)
                    {
                        // 跨字段的写入按布局拆为逐字段写入（寄存器对、合并的清零等一次写入多个字段）；
                        // 只覆盖字段一部分的段写为读改写：f = (f & ~掩码) | (段 << 位移)。
                        foreach (var part in leaves)
                        {
                            var leaf = part.Leaf;
                            var leafTarget = LocationValue(leaf, store.Address, store: true);
                            var slice = values.Syms.Slice(operands[1], part.Bit, part.Width);
                            ManagedValue leafValue;
                            if (part.FieldBit == 0 && part.Width == (ManagedTypes.IsReferenceType(leaf.Type) ? 64 : types.Size(leaf.Type) * 8))
                                leafValue = View(slice, leaf.Type, store.Address);
                            else if (types.Kind(leaf.Type) is TypeKind.Int or TypeKind.Bool && IntegerBits(slice, leaf.Type, store.Address) is { } bits)
                            {
                                var width = Width(leaf.Type);
                                var mask = Expr.Mask(part.Width) << part.FieldBit;
                                ManagedValue shifted = part.FieldBit == 0 ? bits : new BinaryValue(BinOp.Shl, bits, new ConstantValue((ulong)part.FieldBit, types.Int32, 32), leaf.Type, width);
                                var kept = new BinaryValue(BinOp.And, LocationValue(leaf, store.Address), new ConstantValue(~mask & Expr.Mask(width), leaf.Type, width), leaf.Type, width);
                                leafValue = new BinaryValue(BinOp.Or, kept, shifted, leaf.Type, width);
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
