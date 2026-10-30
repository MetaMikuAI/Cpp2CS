using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery;

internal sealed class TypesState
{
    internal readonly Dictionary<Variable, TypeRef> known = new();
    internal readonly HashSet<Variable> phiInProgress = [];
    internal Dictionary<Variable, TypeRef>? typingSeeds;
    internal Dictionary<Variable, TypeResult>? syncedSolution;
}
