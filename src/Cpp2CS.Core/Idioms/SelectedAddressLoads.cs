using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>常量偏移的条件选择改为条件读取；字段身份仍由后续内存模型核对。</summary>
internal static class SelectedAddressLoads
{
    public static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        static bool Pure(Expr value) => !ExprMap.Walk(value).Any(e => e is Load or Intrinsic or Unknown
            or Binary { Op: BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem });
        Select? Choice(Expr address, HashSet<Variable> seen)
        {
            if (address is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value))
                return value is Use or Select ? Choice(value, seen) : null;
            if (address is Select { Width: 64, True: Const, False: Const } select && Pure(select.Condition)) return select;
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
                if (block.Statements[i] is not Define define) continue;
                var value = ExprMap.Map(define.Value, expression => expression is Load load && Choice(load.Address, []) is { } choice
                    ? new Select(choice.Condition, load with { Address = choice.True }, load with { Address = choice.False }, load.Width) : null);
                if (ReferenceEquals(value, define.Value)) continue;
                block.Statements[i] = define with { Value = value };
                changed = true;
            }
        return changed;
    }
}
