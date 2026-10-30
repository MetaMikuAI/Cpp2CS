using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class StaticFieldPhiLoadsPass
{
    internal static bool StaticFieldPhiLoads(this IdiomState state)
    {
        Expr ResolveMetadata(Expr expression)
        {
            var mapped = ExprMap.Map(expression, part => !ReferenceEquals(part, expression) ? ResolveMetadata(part) : null);
            var part = mapped;
            if (part is not Load { Width: 64 } load)
                return mapped;
            if (load.Address is Const address)
            {
                if (state.facts.Usages.At(address.Value) is { } usage)
                    return new Symbol(SymbolOfPass.SymbolOf(usage.Usage.Kind), usage.Usage.Value);
                if (state.facts.Model.Image.RelocatedPointer(address.Value) is { } pointer && state.facts.Usages.At(pointer) is not null)
                    return Expr.C(pointer, 64);
            }

            return SplitPass.Split(load.Address) is (Symbol { Kind: SymbolKind.Class } type, RuntimeLayout.ClassStaticFields) ? new Symbol(SymbolKind.StaticFields, type.Value) : mapped;
        }

        var changed = false;
        foreach (var block in state.function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (block.Predecessors.Any(p => p.NormalSuccessors.Count() != 1 || p.Handler == block))
                    continue;
                foreach (var statement in block.Statements.Where(s => s is not Phi).ToArray())
                {
                    if (statement is not Define && statement is not Return)
                        break;
                    foreach (var load in ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>().ToArray())
                    {
                        var expanded = state.defs.Expand(load);
                        if (!ExprMap.Walk(expanded).OfType<Use>().Any(u => u.Variable == phi.Target))
                            continue;
                        var values = phi.Sources.Select(v => ResolveMetadata(ExprMap.Map(expanded, part => part is Use use && use.Variable == phi.Target ? state.defs.Expand(new Use(v, v.Width)) : null))).ToArray();
                        if (values.Any(v => v is not Load l || SplitPass.Split(l.Address).Basis is not (Symbol { Kind: SymbolKind.StaticFields } or Use)))
                            continue;
                        var target = state.Fresh();
                        var incoming = new Variable[values.Length];
                        for (var i = 0; i < values.Length; i++)
                        {
                            var parent = block.Predecessors[i];
                            var last = parent.Statements.LastOrDefault();
                            incoming[i] = state.Fresh();
                            parent.Statements.Insert(parent.Statements.Count - (last is Jump or Branch or IndirectJump or Return ? 1 : 0), new Define(last?.Address ?? parent.Start, incoming[i], values[i]));
                        }

                        block.Statements.Insert(block.Statements.IndexOf(phi) + 1, new Phi(phi.Address, target, incoming));
                        var position = block.Statements.IndexOf(statement);
                        if (position >= 0)
                            block.Statements[position] = ExprMap.MapOperands(statement, e => ExprMap.Map(e, part => part == load ? new Use(target, load.Width) : null));
                        changed = true;
                    }
                }
            }

        return changed;
    }
}
