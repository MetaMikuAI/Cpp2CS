using Cpp2CS.Ir;
namespace Cpp2CS.Idioms;

internal static class InitializedClassLoadsPass
{
    internal static bool InitializedClassLoads(this IdiomState state)
    {
        return ClassInitializationFacts.Run(state.function, constructorFacts: state.self?.Method.Name != ".cctor");
    }
}
