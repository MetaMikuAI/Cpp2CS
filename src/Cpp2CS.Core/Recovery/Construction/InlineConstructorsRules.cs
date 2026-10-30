using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class InlineConstructorsRules
{
    internal static bool InlineConstructor(this RecoveryScope ctx, Block block, int index, Call allocation, DefinitionRef type, Variable created)
    {
        InlineConstructors.Match? match = null;
        foreach (var constructor in type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
        {
            if (ctx.owner.ConstructorPattern(new(constructor, type.Arguments, [])) is not { } pattern || InlineConstructors.Find(pattern, ctx.function, block, index, created) is not { } candidate)
                continue;
            if (match is not null)
                return false;
            match = candidate;
        }

        if (match is null)
            return false;
        ctx.State.Construction.inlineConstructors[allocation] = match;
        ctx.State.Lowering.dropped.UnionWith(match.Statements);
        return true;
    }
}
