using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>成功的类布局初始化不会失效；只消除被先前初始化支配的重复操作和标志位判断。</summary>
internal static class ClassInitializationFacts
{
    private sealed record Point(Block Block, int Index, Stmt Statement);

    /// <summary>
    /// beforefieldinit 类型的初始化时机不受约束（ECMA-335 II.10.5.3：首次访问静态字段之前的任意时刻），运行时在字段访问处自行保证。
    /// IL2CPP 在调用这类类型的方法之前写的显式初始化没有对应的 IL，从这里起不再存在。
    /// </summary>
    internal static bool DropUnconstrained(MachineFunction function)
    {
        var changed = false;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Op: { Kind: OpKind.RunClassConstructor, Operand: DefinitionRef type }, Defines.Length: 0 } call
                    && (type.Definition.Attributes & System.Reflection.TypeAttributes.BeforeFieldInit) != 0)
                {
                    block.Statements[i] = new Nop(call.Address, "beforefieldinit 类型的显式初始化");
                    changed = true;
                }
        return changed;
    }

    internal static bool Run(MachineFunction function, bool constructorFacts = true)
    {
        var points = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => new Point(b, i, s))).ToArray();
        var initializers = points.Where(p => p.Statement is Call { Op: { Kind: OpKind.InitClass or OpKind.RunClassConstructor, Operand: TypeRef } }).ToArray();
        if (initializers.Length == 0) return false;
        var definitions = points.Where(p => p.Statement is Define).ToDictionary(p => ((Define)p.Statement).Target);
        var dominators = Dominators.Compute(function);
        bool Initialized(TypeRef type, OpKind kind, Point at) => initializers.Any(p => ((Call)p.Statement).Op is { } op
            && (constructorFacts || kind == OpKind.InitClass) && op.Kind == kind && Equals(op.Operand, type) && dominators.Dominates(p.Block.Index, at.Block.Index)
            && (p.Block != at.Block || p.Index < at.Index));
        bool InitializationBit(Expr value, Point at, HashSet<Variable> seen) => value switch
        {
            Use u when seen.Add(u.Variable) && definitions.TryGetValue(u.Variable, out var definition)
                => InitializationBit(((Define)definition.Statement).Value, definition, seen),
            Ir.Convert c when c.Kind is ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate => InitializationBit(c.Operand, at, seen),
            Extract { Low: 0 } e => InitializationBit(e.Operand, at, seen),
            Load
            {
                Width: 8 or 16, Address: Binary
                {
                    Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type },
                    Right: Const { Value: RuntimeLayout.ClassBitflags1 }
                }
            } => Initialized(type, OpKind.InitClass, at),
            _ => false,
        };
        var changed = false;
        foreach (var point in points)
        {
            var statement = point.Statement;
            if (statement is Call { Op: { Kind: OpKind.InitClass, Operand: TypeRef type }, Arguments: [var subject] } call
                && call.Defines.Length <= 1 && Initialized(type, OpKind.InitClass, point))
            {
                point.Block.Statements[point.Index] = call.Defines is [var result] ? new Define(call.Address, result, subject) : new Nop(call.Address, "类布局已初始化");
                changed = true;
                continue;
            }
            point.Block.Statements[point.Index] = ExprMap.MapOperands(statement, e =>
            {
                var mapped = ExprMap.Map(e, value =>
                {
                    if (value is Load
                        {
                            Width: 32, Address: Binary
                            {
                                Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type },
                                Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor }
                            }
                        }
                        && Initialized(type, OpKind.RunClassConstructor, point))
                    { changed = true; return Expr.C(1, 32); }
                    if (value is Binary { Op: BinOp.And } mask
                        && (mask.Right is Const { Value: 1 } && InitializationBit(mask.Left, point, [])
                            || mask.Left is Const { Value: 1 } && InitializationBit(mask.Right, point, [])))
                    { changed = true; return Expr.C(1, mask.Width); }
                    return null;
                });
                return ReferenceEquals(e, mapped) ? e : Fold.Simplify(mapped);
            });
        }
        return changed;
    }
}
