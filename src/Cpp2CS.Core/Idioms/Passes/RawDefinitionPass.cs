using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RawDefinitionPass
{
    internal static Expr? RawDefinition(this IdiomState state, Expr e) => e is Use { Variable: var v } ? state.defs.Raw(v) : null;
}
