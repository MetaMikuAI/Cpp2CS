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
        foreach (var read in Reads(statement).Concat(aggregateReadSites.GetValueOrDefault(statement) ?? []).Where(materialized.Contains))
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
                    if (aggregateStores.Contains(store)) return null;
                    if (AggregateStore(block, index) is { } aggregate)
                    {
                        var destination = LocationValue(aggregate.Target, store.Address, store: true);
                        var value = View(aggregate.Value, aggregate.Target.Type, store.Address);
                        output.Add(destination is LocalValue local ? new ManagedAssignment(store.Address, local, value) : new ManagedStore(store.Address, destination, value));
                        return null;
                    }
                    var location = oracle.Locate(operands[0], store.Value.Width);
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
                    var target = LocationValue(location, store.Address, store: true);
                    var stored = View(operands[1], location.Type, store.Address);
                    output.Add(target is LocalValue whole ? new ManagedAssignment(store.Address, whole, stored) : new ManagedStore(store.Address, target, stored));
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
            case IndirectJump { Targets.Length: > 0 } jump when TableIndex(operands[0]) is { } tableIndex:
                return new Switch(jump.Address, View(tableIndex, types.Int32, jump.Address), jump.Targets);
            case IndirectJump jump:
                return Fail(jump.Address, "控制 间接跳转的目标集合或下标未知", terminal: true);
            default:
                return Fail(statement.Address, $"语句 {statement.GetType().Name}", terminal: false) is Statement s ? AddHole(output, s) : null;
        }
    }

    /// <summary>跳转表的下标：目标中唯一一次读取的地址为常量表基址加比例下标。</summary>
    private Sym? TableIndex(Sym target)
    {
        var stack = new Stack<Sym>();
        stack.Push(target);
        Sym? found = null;
        while (stack.Count > 0)
        {
            switch (SymTable.Resolve(stack.Pop()))
            {
                case ReadSym read:
                    if (found is not null) return null;
                    // 表基址为常量：比例下标，或唯一的变量项（字节表的比例为 1）。
                    var (root, _, index, _) = oracle.Decompose(read.Address);
                    index ??= root is ConstSym || ReferenceEquals(root, SymTable.Resolve(read.Address)) ? null : root;
                    if (index is null) return null;
                    found = index;
                    break;
                case SliceSym slice: stack.Push(slice.Base); break;
                case ConcatSym concat: foreach (var part in concat.Parts) stack.Push(part); break;
                case OpSym op: foreach (var arg in op.Args) stack.Push(arg); break;
            }
        }
        return found;
    }

    private static Terminator? AddHole(List<ManagedStatement> output, Statement hole)
    {
        output.Add(hole.Value);
        return null;
    }

    private IEnumerable<ReadSym> Reads(Stmt statement)
    {
        var found = new List<ReadSym>();
        void Walk(Sym sym, HashSet<Sym> seen)
        {
            sym = SymTable.Resolve(sym);
            if (!seen.Add(sym)) return;
            switch (sym)
            {
                case ReadSym read:
                    Walk(read.Address, seen);
                    if (ReferenceEquals(read.Site, statement)) found.Add(read);
                    break;
                case SliceSym slice: Walk(slice.Base, seen); break;
                case ConcatSym concat: foreach (var part in concat.Parts) Walk(part, seen); break;
                case OpSym op: foreach (var arg in op.Args) Walk(arg, seen); break;
            }
        }
        var visited = new HashSet<Sym>();
        foreach (var operand in values.Operands(statement)) Walk(operand, visited);
        return found.OrderBy(r => r.Ordinal);
    }

    private ManagedValue? ReturnValue(Return ret, IReadOnlyList<Sym> operands)
    {
        var type = oracle.ReturnType;
        if (ManagedTypes.IsVoid(type)) return null;
        if (ret.Pieces.Length == 0) return Hole(ret.Address, "返回 返回值缺失", type);
        var width = analysis.Signature.Return is { } r ? MethodEnvironment.ValueWidth(r) : Width(type);
        var bits = new Sym?[width];
        var parts = new List<Sym>();
        var at = 0;
        foreach (var (piece, sym) in ret.Pieces.Zip(operands.Skip(ret.Value is null ? 0 : 1)).OrderBy(p => p.First.Offset))
        {
            var start = piece.Offset * 8;
            if (start > at) parts.Add(values.Syms.Undef(start - at));
            if (start < at) continue;
            var size = Math.Min(sym.Width, width - start);
            parts.Add(values.Syms.Slice(sym, 0, size));
            at = start + size;
        }
        if (at < width) parts.Add(values.Syms.Undef(width - at));
        return View(values.Syms.Concat(parts), type, ret.Address);
    }
}
