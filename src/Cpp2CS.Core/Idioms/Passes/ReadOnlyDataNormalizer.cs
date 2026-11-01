using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>只读常量与有上界证明的查表；重定位项须指向已知元数据槽，不把地址当作数值。</summary>
internal static class ReadOnlyDataNormalizer
{
    public static bool Run(MachineFunction function, ImageDocument image, Func<ulong, bool>? metadataSlot = null)
    {
        var dominators = Dominators.Compute(function);
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Address(Expr expression, int depth = 0) => depth >= 16 ? expression : Fold.Simplify(ExprMap.Map(expression, value =>
            value is Use use && definitions.TryGetValue(use.Variable, out var definition) && definition.Width >= use.Width
                && !ExprMap.Walk(definition).Any(e => e is Load or Ir.Read or Intrinsic or Unknown)
                ? Address(Fold.Convert(ConvKind.Truncate, definition, use.Width), depth + 1) : null));
        var jumpLoads = new HashSet<Load>();
        var visited = new HashSet<Variable>();
        void JumpValues(Expr expression)
        {
            foreach (var part in ExprMap.Walk(expression))
                if (part is Load load) jumpLoads.Add(load);
                else if (part is Use use && visited.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value)) JumpValues(value);
        }
        foreach (var jump in function.Blocks.SelectMany(b => b.Statements).OfType<IndirectJump>()) JumpValues(jump.Target);
        var changed = false;
        Expr Rewrite(Expr expression, Block block, Expr[] guards) => ExprMap.Map(expression, value =>
                {
                    // 条件地址拆成单臂读取后，上界只在被选中的那一臂有效。
                    if (value is Select select)
                    {
                        var yes = Rewrite(select.True, block, [.. guards, select.Condition]);
                        var no = Rewrite(select.False, block, [.. guards, Fold.Not(select.Condition)]);
                        return ReferenceEquals(yes, select.True) && ReferenceEquals(no, select.False) ? select : select with { True = yes, False = no };
                    }
                    if (value is not Load load || jumpLoads.Contains(load) || load.Width is not (8 or 16 or 32 or 64 or 128)) return null;
                    var addressValue = Address(load.Address);
                    if (addressValue is Const address && Readable(address.Value, load.Width / 8))
                    {
                        changed = true;
                        return Read(address.Value, load.Width);
                    }
                    if (load.Width == 128 || addressValue is not Binary { Op: BinOp.Add, Right: Const table } sum) return null;
                    Expr index = sum.Left;
                    if (index is Binary { Op: BinOp.Shl, Right: Const shift } scaled && (1UL << (int)shift.Value) == (ulong)load.Width / 8)
                        index = scaled.Left;
                    else if (load.Width != 8) return null;
                    var signedWidth = 0;
                    if (index is Ir.Convert { Kind: ConvKind.SignExtend or ConvKind.ZeroExtend } extension)
                    {
                        if (extension.Kind == ConvKind.SignExtend) signedWidth = extension.Operand.Width;
                        index = extension.Operand;
                    }
                    // 同一 SSA 快照的高位已由扩展确定；无符号上界排除了符号扩展的负数。
                    else if (index is Use { Width: 64 } use && definitions.TryGetValue(use.Variable, out var definition)
                        && definition is Ir.Convert { Kind: ConvKind.SignExtend or ConvKind.ZeroExtend, Width: 64, Operand.Width: 32 })
                        index = new Use(use.Variable, 32);
                    var count = Bound(index, block, guards);
                    if (signedWidth is > 0 and < 32 && count > 1 << (signedWidth - 1)) return null;
                    if (count is < 1 or > 256) return null;
                    var size = count * load.Width / 8;
                    var pointers = load.Width == 64 && (table.Value & 7) == 0 && ReadOnlyPointers(table.Value, size);
                    if (!pointers && !Readable(table.Value, size)) return null;
                    Expr Cell(int index) => pointers ? Expr.C(image.RelocatedPointer(table.Value + (ulong)index * 8)!.Value, 64)
                        : Read(table.Value + (ulong)index * (ulong)load.Width / 8, load.Width);
                    Expr result = Cell(count - 1);
                    for (var k = count - 2; k >= 0; k--)
                        result = new Select(new Compare(Cond.Eq, index, Expr.C((ulong)k, index.Width)),
                            Cell(k), result, load.Width);
                    changed = true;
                    return result;
                });
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is not IndirectJump)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => Rewrite(e, block, []));
        return changed;

        int Bound(Expr index, Block block, Expr[] guards)
        {
            int Limit(Expr value, HashSet<Variable> active) => value switch
            {
                Const { Value: < 256 } c => (int)c.Value + 1,
                Compare or Logical or Not => 2,
                Select choice when Limit(choice.True, new(active)) is > 0 and var yes && Limit(choice.False, new(active)) is > 0 and var no => Math.Max(yes, no),
                Binary { Op: BinOp.And, Right: Const { Value: < 256 } mask } => (int)mask.Value + 1,
                Ir.Convert { Kind: ConvKind.ZeroExtend } convert => Limit(convert.Operand, active),
                Use use when active.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var definition) => Limit(definition, active),
                _ => 0,
            };
            if (Limit(index, []) is > 0 and var intrinsic) return intrinsic;
            bool SameIndex(Expr compared)
            {
                var checkedValue = IndexValue(compared, definitions);
                var loadedValue = IndexValue(index, definitions);
                if (checkedValue == loadedValue) return true;
                // 无符号检查显式屏蔽高位时，与窄索引观察同一组位；不合并任意不同宽度快照。
                if (checkedValue is Binary { Op: BinOp.And, Right: Const mask } masked && index.Width is 8 or 16
                    && mask.Value == Expr.Mask(index.Width))
                    return IndexValue(Fold.Convert(ConvKind.Truncate, masked.Left, index.Width), definitions) == loadedValue;
                return false;
            }
            foreach (var guard in guards)
                if (guard is Compare { Cond: Cond.Ult or Cond.Ule, Left: var compared, Right: Const { Value: <= 256 } limit } test
                    && SameIndex(compared))
                    return (int)limit.Value + (test.Cond == Cond.Ule ? 1 : 0);
            foreach (var parent in function.Blocks)
            {
                if (!dominators.Dominates(parent.Index, block.Index)
                    || parent.Statements.LastOrDefault() is not Branch { Condition: Compare { Left: var compared, Right: Const limit } condition } branch
                    || condition.Cond is not (Cond.Ult or Cond.Ule or Cond.Uge or Cond.Ugt)
                    || !SameIndex(compared) || limit.Value > 256) continue;
                var count = (int)limit.Value + (condition.Cond is Cond.Ule or Cond.Ugt ? 1 : 0);
                if (count is < 1 or > 256) continue;
                var destination = condition.Cond switch
                { Cond.Ult or Cond.Ule => branch.Target, Cond.Uge or Cond.Ugt => branch.Fallthrough, _ => 0UL };
                var child = parent.NormalSuccessors.FirstOrDefault(b => b.Start == destination);
                if (child is not null && child.Predecessors.Count == 1 && dominators.Dominates(child.Index, block.Index)) return count;
            }
            return 0;
        }

        bool Readable(ulong address, int size)
        {
            var section = image.SectionAt(address);
            if (section is null || section.Executable || (section.Flags & 1) != 0 || !section.Contains(address + (ulong)size - 1)
                || image.ReadUpTo(address, size).Length != size) return false;
            for (var offset = -7; offset < size; offset++)
                if (image.RelocatedPointer(unchecked(address + (ulong)offset)) is not null || image.Imports.ContainsKey(unchecked(address + (ulong)offset))) return false;
            return true;
        }

        bool ReadOnlyPointers(ulong address, int size)
        {
            var section = image.SectionAt(address);
            if (metadataSlot is null || section is null || section.Executable || !section.Contains(address + (ulong)size - 1)
                || image.ReadUpTo(address, size).Length != size) return false;
            if ((section.Flags & 1) != 0 && !image.RelroRanges.Any(r => address >= r.Address && address - r.Address < r.Size
                && (ulong)size <= r.Size - (address - r.Address))) return false;
            for (var offset = 0; offset < size; offset += 8)
                if (image.Imports.ContainsKey(address + (ulong)offset) || image.RelocatedPointer(address + (ulong)offset) is not { } pointer
                    || !metadataSlot(pointer)) return false;
            return true;
        }

        Expr Read(ulong address, int width)
        {
            if (width == 128)
                return new Insert(new Insert(Expr.C(0, 128), Read(address, 64), 0), Read(address + 8, 64), 64);
            ulong bits = 0;
            var bytes = image.Read(address, width / 8);
            for (var i = 0; i < bytes.Length; i++) bits |= (ulong)bytes[i] << (8 * i);
            return Expr.C(bits, width);
        }
    }

    /// <summary>比较检查与查表的同宽 SSA 索引；不展开内存读取，避免混同不同时间的快照。</summary>
    internal static Expr IndexValue(Expr index, IReadOnlyDictionary<Variable, Expr> definitions)
    {
        var seen = new HashSet<Variable>();
        while (index is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value)
            && value.Width >= use.Width && !ExprMap.Walk(value).Any(e => e is Load or Read or Intrinsic or Unknown))
            index = Fold.Simplify(Fold.Convert(ConvKind.Truncate, value, use.Width));
        return index;
    }
}
