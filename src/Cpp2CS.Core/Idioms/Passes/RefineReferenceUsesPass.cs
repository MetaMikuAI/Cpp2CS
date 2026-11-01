using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class RefineReferenceUsesPass
{
    internal static void RefineReferenceUses(this IdiomState state, Block start, int position, Use obj, Variable cast, Dominators dominators) => CheckedClassValues.Refine(state.function, start, position, obj, cast, dominators);
}
