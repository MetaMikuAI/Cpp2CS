using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class EnumElementClassesPass
{
    internal static bool EnumElementClasses(this IdiomState state)
    {
        var results = state.All.OfType<Call>().Where(c => c.Defines.Length > 0).ToDictionary(c => c.Defines[0]);
        Call? Source(Expr value) => state.defs.Expand(value) is Use u ? results.GetValueOrDefault(u.Variable) : null;
        bool Named(Call? call, string ownerName, string name) => call is { Op: null, Target: Const target } && state.facts.EntriesAt(target.Value).Any(e => e.Method is { } m && m.Method.Owner.FullName == ownerName && m.Method.Name == name);
        TypeRef? Element(Expr value)
        {
            var current = Source(value);
            Call? array;
            if (Named(current, "System.Array", "GetValue") && current!.Arguments.Length > 0)
                array = Source(current.Arguments[0]);
            else
            {
                if (current is not { Op: { Kind: OpKind.CallInterface, Operand: (DefinitionRef { Definition.FullName: "System.Collections.IEnumerator" }, 1) }, Arguments: [var iterator, ..] })
                    return null;
                var enumerator = Source(iterator);
                if (!Named(enumerator, "System.Array", "GetEnumerator") || enumerator!.Arguments.Length == 0)
                    return null;
                array = Source(enumerator.Arguments[0]);
            }

            if (!Named(array, "System.Enum", "GetValues") || array!.Arguments.Length == 0)
                return null;
            var type = Source(array.Arguments[0]);
            return Named(type, "System.Type", "GetTypeFromHandle") && type!.Arguments.Length > 0 && state.defs.Expand(type.Arguments[0]) is Symbol { Kind: SymbolKind.Type, Value: DefinitionRef { Definition.IsEnum: true } item } ? item : null;
        }

        var changed = false;
        TypeRef? ElementClass(Expr expression)
        {
            if (state.defs.Expand(expression) is not Load { Width: 64, Address: var address })
                return null;
            return SplitPass.Split(address) switch
            {
                (Load { Width: 64, Address: var instance }, RuntimeLayout.ClassElementClass) => Element(instance),
                (Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }, RuntimeLayout.ClassElementClass) => type,
                _ => null,
            };
        }

        Expr? Replace(Expr expression)
        {
            if (expression is not Compare { Cond: Cond.Eq or Cond.Ne } compare || ElementClass(compare.Left) is not { } left || !left.Equals(ElementClass(compare.Right)))
                return null;
            changed = true;
            return Expr.C(compare.Cond == Cond.Eq ? 1UL : 0, 1);
        }

        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Replace));
        return changed;
    }
}
