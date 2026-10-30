
namespace Cpp2CS.Idioms;

internal static class InitializedClassLoadsPass
{
    internal static bool InitializedClassLoads(this IdiomState state) => state.self?.Method.Name != ".cctor" && ClassInitializationFacts.Run(state.function);
}
