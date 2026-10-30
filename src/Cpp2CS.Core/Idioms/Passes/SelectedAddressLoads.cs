using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>条件地址改为单臂读取；已走过的分支可确认引用别名，字段身份仍由内存模型核对。</summary>
internal static class SelectedAddressLoads
{
    public static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        static bool Pure(Expr value) => !ExprMap.Walk(value).Any(e => e is Load or Intrinsic or Unknown
            or Binary { Op: BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem });
        static bool? KnownSide(Block block, Expr condition)
        {
            // 只沿唯一前驱追踪同一 SSA 条件；可重读的内存和未转换的寄存器不能作为路径事实。
            if (!Pure(condition) || ExprMap.Walk(condition).Any(e => e is Read or Use { Variable.Version: < 0 })) return null;
            var seen = new HashSet<Block> { block };
            while (block.Predecessors.ToArray() is [var parent] && seen.Add(parent))
            {
                if (parent.Statements.LastOrDefault() is Branch branch && branch.Condition == condition
                    && branch.Target != branch.Fallthrough && parent.NormalSuccessors.Contains(block))
                    return block.Start == branch.Target;
                block = parent;
            }
            return null;
        }
        Select? Choice(Expr address, HashSet<Variable> seen)
        {
            if (address is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value))
                return value is Use or Select ? Choice(value, seen) : null;
            if (address is Select { Width: 64 } select && Pure(select.Condition) && Pure(select.True) && Pure(select.False)) return select;
            if (address is not Binary { Op: BinOp.Add, Width: 64 } add) return null;
            if (Pure(add.Right) && Choice(add.Left, seen) is { } left)
                return left with { True = Fold.Simplify(add with { Left = left.True }), False = Fold.Simplify(add with { Left = left.False }) };
            if (Pure(add.Left) && Choice(add.Right, seen) is { } right)
                return right with { True = Fold.Simplify(add with { Right = right.True }), False = Fold.Simplify(add with { Right = right.False }) };
            return null;
        }
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                var rewritten = ExprMap.MapOperands(statement, operand => ExprMap.Map(operand, expression =>
                {
                    if (expression is Use use && definitions.TryGetValue(use.Variable, out var definition)
                        && definition is Select { True: Use or Const or Symbol or FrameAddress, False: Use or Const or Symbol or FrameAddress } alias
                        && use.Width == alias.Width && KnownSide(block, alias.Condition) is { } aliasSide)
                        return aliasSide ? alias.True : alias.False;
                    if (expression is Select { True: Load, False: Load } selected
                        && KnownSide(block, selected.Condition) is { } selectedSide) return selectedSide ? selected.True : selected.False;
                    if (statement is not Define || expression is not Load load || Choice(load.Address, []) is not { } choice) return null;
                    return KnownSide(block, choice.Condition) is { } side ? load with { Address = side ? choice.True : choice.False }
                        : new Select(choice.Condition, load with { Address = choice.True }, load with { Address = choice.False }, load.Width);
                }));
                if (ReferenceEquals(rewritten, statement)) continue;
                block.Statements[i] = rewritten;
                changed = true;
            }
        return changed;
    }
}
