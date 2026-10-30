using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ArrayPointerLoopsPass
{
    internal static bool ArrayPointerLoops(this IdiomState state)
    {
        var arrays = state.All.OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } a } && ManagedTypes.IsReferenceType(a.Element) && c.Defines.FirstOrDefault() is not null).Select(c => c.Defines[0]).ToHashSet();
        Use Root(Use value)
        {
            var seen = new HashSet<Variable>();
            while (seen.Add(value.Variable) && state.RawDefinition(value) is Use copy)
                value = copy;
            return value;
        }

        var changed = false;
        foreach (var block in state.function.Blocks)
            foreach (var pointer in block.Statements.OfType<Phi>().Where(p => p.Sources.Length == 2).ToArray())
            {
                for (var seed = 0; seed < 2; seed++)
                {
                    if (state.RawDefinition(new Use(pointer.Sources[seed], 64)) is not Binary { Op: BinOp.Add, Left: Use array, Right: Const { Value: 32 } } || !arrays.Contains(Root(array).Variable) || state.RawDefinition(new Use(pointer.Sources[1 - seed], 64)) is not Binary { Op: BinOp.Add, Left: Use previous, Right: Const { Value: 8 } } || previous.Variable != pointer.Target)
                        continue;
                    var index = block.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources.Length == 2 && state.RawDefinition(new Use(p.Sources[seed], 64)) is Const { Value: 0 } && state.RawDefinition(new Use(p.Sources[1 - seed], 64)) is Binary { Op: BinOp.Add, Left: Use prior, Right: Const { Value: 1 }, Width: 64 } && prior.Variable == p.Target);
                    if (index is null)
                        continue;
                    block.Statements.Remove(pointer);
                    var address = new Binary(BinOp.Add, new Binary(BinOp.Add, array, Expr.C(32, 64), 64), new Binary(BinOp.Shl, new Use(index.Target, 64), Expr.C(3, 64), 64), 64);
                    foreach (var current in state.function.Blocks)
                        for (var i = 0; i < current.Statements.Count; i++)
                            current.Statements[i] = ExprMap.MapOperands(current.Statements[i], e => ExprMap.Map(e, part => part is Use use && use.Variable == pointer.Target ? address : null));
                    changed = true;
                    break;
                }
            }

        return changed;
    }
}
