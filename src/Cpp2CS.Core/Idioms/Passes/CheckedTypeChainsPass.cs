using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class CheckedTypeChainsPass
{
    internal static bool CheckedTypeChains(this IdiomState state)
    {
        var changed = false;
        foreach (var head in state.function.Blocks)
            for (var index = 0; index < head.Statements.Count; index++)
            {
                if (head.Statements[index] is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ult } depth] } first || StripConversionsPass.StripConversions(state.defs.Expand(depth.Left)) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } objectDepth } || StripConversionsPass.StripConversions(state.defs.Expand(depth.Right)) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class } type, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } })
                    continue;
                var klass = StripConversionsPass.StripConversions(state.RawDefinition(StripConversionsPass.StripConversions(depth.Left)) ?? depth.Left);
                var objectClass = klass is Load { Address: Binary { Left: var basis } } ? basis : objectDepth.Left;
                var hierarchy = new Load(Fold.Simplify(new Binary(BinOp.Add, objectDepth.Left, Expr.C(RuntimeLayout.ClassTypeHierarchy, 64), 64)), 64);
                foreach (var (block, statement) in Cpp2CS.Idioms.AllocationPairing.Following(head, index))
                {
                    if (statement is Define or Nop)
                        continue;
                    if (statement is not Call { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne } compare] } second)
                        break;
                    var expanded = state.defs.Expand(compare);
                    if (expanded is not Compare test || test.Right != type || test.Left is not Load { Width: 64 } item || !TermsPass.Terms(item.Address).Contains(hierarchy))
                        break;
                    var result = state.Fresh();
                    head.Statements.Insert(index, new Call(first.Address, CallKind.Direct, Expr.C(0, 64)) { Op = new RuntimeOp(OpKind.TypeCheck, type.Value), Arguments = [objectClass], Results = [result.Storage], Defines = [result], });
                    head.Statements[++index] = first with
                    {
                        Arguments = [new Compare(Cond.Eq, new Use(result, 64), Expr.C(0, 64))]
                    };
                    block.Statements[block.Statements.IndexOf(second)] = new Nop(second.Address, "TypeCheck");
                    state.Result.Hit(Template.InlineTypeCheck);
                    changed = true;
                    break;
                }
            }

        return changed;
    }
}
