using Cpp2CS.Flow;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>只读常量与有上界证明的数值查表；不把可写槽位、重定位指针或跳转地址当作数值。</summary>
internal static class ReadOnlyDataNormalizer
{
    public static bool Run(MachineFunction function, ImageDocument image)
    {
        var dominators = Dominators.Compute(function);
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
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
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is IndirectJump) continue;
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, value =>
                {
                    if (value is not Load load || jumpLoads.Contains(load) || load.Width is not (8 or 16 or 32 or 64 or 128)) return null;
                    if (load.Address is Const address && Readable(address.Value, load.Width / 8))
                    {
                        changed = true;
                        return Read(address.Value, load.Width);
                    }
                    if (load.Width == 128 || load.Address is not Binary { Op: BinOp.Add, Right: Const table } sum) return null;
                    Expr index = sum.Left;
                    if (index is Binary { Op: BinOp.Shl, Right: Const shift } scaled && (1UL << (int)shift.Value) == (ulong)load.Width / 8)
                        index = scaled.Left;
                    else if (load.Width != 8) return null;
                    if (index is Ir.Convert { Kind: ConvKind.SignExtend or ConvKind.ZeroExtend } extension) index = extension.Operand;
                    var count = Bound(index, block);
                    if (count is < 1 or > 256 || !Readable(table.Value, count * load.Width / 8)) return null;
                    Expr result = Read(table.Value + (ulong)(count - 1) * (ulong)load.Width / 8, load.Width);
                    for (var k = count - 2; k >= 0; k--)
                        result = new Select(new Compare(Cond.Eq, index, Expr.C((ulong)k, index.Width)),
                            Read(table.Value + (ulong)k * (ulong)load.Width / 8, load.Width), result, load.Width);
                    changed = true;
                    return result;
                }));
            }
        return changed;

        int Bound(Expr index, Block block)
        {
            foreach (var parent in function.Blocks)
            {
                if (!dominators.Dominates(parent.Index, block.Index)
                    || parent.Statements.LastOrDefault() is not Branch { Condition: Compare { Left: var compared, Right: Const limit } condition } branch
                    || compared != index || limit.Value is 0 or > 256) continue;
                var destination = condition.Cond switch { Cond.Ult => branch.Target, Cond.Uge => branch.Fallthrough, _ => 0UL };
                var child = parent.NormalSuccessors.FirstOrDefault(b => b.Start == destination);
                if (child is not null && child.Predecessors.Count == 1 && dominators.Dominates(child.Index, block.Index)) return (int)limit.Value;
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
}
