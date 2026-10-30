using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ArrayAddressPhisPass
{
    internal static bool ArrayAddressPhis(this IdiomState state)
    {
        var allocations = state.All.OfType<Call>().Where(c => c.Op is { Kind: OpKind.NewArray, Operand: ArrayRef { IsVector: true } a } && ManagedTypes.IsReferenceType(a.Element) && c.Defines.FirstOrDefault() is not null).ToDictionary(c => c.Defines[0], c => c.Op!.Operand);
        Expr MathValue(Expr expression, int depth = 0) => depth > 12 ? expression : ExprMap.Map(expression, e => e is Use use && state.RawDefinition(use) is (Binary or Ir.Convert) and var value ? MathValue(value, depth + 1) : null);
        Expr? Index(Expr offset) => MathValue(offset) switch
        {
            Const { Value: 0 } => Expr.C(0, 64),
            Binary { Op: BinOp.Shl, Right: Const { Value: 3 }, Left: var value } => value,
            Binary { Op: BinOp.AShr, Right: Const { Value: 29 }, Left: Binary { Op: BinOp.Shl, Left: var value, Right: Const { Value: 32 } } } => Fold.Convert(ConvKind.SignExtend, Fold.Convert(ConvKind.Truncate, value, 32), 64),
            _ => null,
        };
        var changed = false;
        foreach (var block in state.function.Blocks)
            foreach (var pointer in block.Statements.OfType<Phi>().ToArray())
            {
                if (block.Predecessors.Any(p => p.NormalSuccessors.Count() != 1) || !block.Statements.Contains(pointer))
                    continue;
                foreach (var basis in block.Statements.OfType<Phi>().Where(p => p != pointer).ToArray())
                {
                    if (basis.Sources.Length != pointer.Sources.Length || !basis.Sources.All(allocations.ContainsKey) || basis.Sources.Select(v => allocations[v]).Distinct().Count() != 1)
                        continue;
                    var indices = new List<Expr>();
                    for (var i = 0; i < pointer.Sources.Length; i++)
                    {
                        if (pointer.Sources[i] == basis.Sources[i])
                        {
                            indices.Add(Expr.C(0, 64));
                            continue;
                        }

                        if (state.RawDefinition(new Use(pointer.Sources[i], 64)) is not Binary { Op: BinOp.Add, Left: Use root, Right: var offset } || root.Variable != basis.Sources[i] || Index(offset) is not { } index)
                            break;
                        indices.Add(index);
                    }

                    if (indices.Count != pointer.Sources.Length)
                        continue;
                    var sources = indices.Select(_ => state.Fresh()).ToArray();
                    for (var i = 0; i < indices.Count; i++)
                    {
                        var pred = block.Predecessors[i];
                        pred.Statements.Insert(pred.Statements.Count - (pred.Statements.LastOrDefault() is Jump ? 1 : 0), new Define(pointer.Address, sources[i], indices[i]));
                    }

                    var selected = state.Fresh();
                    block.Statements.Remove(pointer);
                    block.Statements.Insert(0, new Phi(pointer.Address, selected, sources));
                    block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Define(pointer.Address, pointer.Target, new Binary(BinOp.Add, new Use(basis.Target, 64), new Binary(BinOp.Shl, new Use(selected, 64), Expr.C(3, 64), 64), 64)));
                    changed = true;
                    break;
                }
            }

        return changed;
    }
}
