using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class InlineConstructorsRules
{
    internal static bool InlineConstructor(this RecoveryScope ctx, Block block, int index, Call allocation, DefinitionRef type, Variable created)
    {
        InlineConstructors.Match? match = null;
        Func<Expr, TypeRef?>? declaredType = null;
        foreach (var constructor in type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
        {
            if (ctx.owner.ConstructorPattern(new(constructor, type.Arguments, [])) is not { } pattern
                || InlineConstructors.Find(pattern, ctx.function, block, index, created,
                    e => InlineConstructors.CanonicalBoolean(e, v => ctx.values.TryGetValue(v, out var value) ? [value]
                            : ctx.phis.TryGetValue(v, out var phi) ? phi.Sources.Select(s => (Expr)new Use(s, s.Width)).ToArray() : [])
                        || ctx.TypeOfValue(e) is { } valueType && ctx.types.Kind(valueType) == TypeKind.Bool
                        || (declaredType ??= DelegateCallNormalizer.TypeQuery(ctx.facts, ctx.function))(e) is { } declared
                            && ctx.types.Kind(declared) == TypeKind.Bool) is not { } candidate)
                continue;
            match = match is null ? candidate : InlineConstructors.Prefer(match, candidate);
        }

        if (match is null)
            return false;
        ctx.State.Construction.inlineConstructors[allocation] = match;
        ctx.State.Lowering.dropped.UnionWith(match.Statements);
        return true;
    }
}
