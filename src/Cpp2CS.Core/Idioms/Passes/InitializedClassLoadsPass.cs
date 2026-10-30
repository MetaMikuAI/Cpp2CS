using Cpp2CS.Ir;
namespace Cpp2CS.Idioms;

internal static class InitializedClassLoadsPass
{
    internal static bool InitializedClassLoads(this IdiomState state)
    {
        Func<Expr, TypeRef?>? query = null;
        return state.self?.Method.Name != ".cctor" && ClassInitializationFacts.Run(state.function,
            expression => (query ??= DelegateCallNormalizer.TypeQuery(state.facts, state.function))(expression));
    }
}
