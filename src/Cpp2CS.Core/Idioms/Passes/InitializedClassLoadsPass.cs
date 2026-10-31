using Cpp2CS.Ir;
namespace Cpp2CS.Idioms;

internal static class InitializedClassLoadsPass
{
    internal static bool InitializedClassLoads(this IdiomState state)
    {
        Func<Expr, TypeRef?>? query = null;
        return ClassInitializationFacts.Run(state.function,
            expression => (query ??= DelegateCallNormalizer.TypeQuery(state.facts, state.function))(expression),
            constructorFacts: state.self?.Method.Name != ".cctor");
    }
}
