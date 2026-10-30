
namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    public sealed record StackCallWitness(ulong Entry, ulong Site, ulong Store, long Sp, long Slot, MethodRef Method);
    internal readonly HashSet<StackCallWitness> stackCalls = [];
    public IReadOnlyCollection<StackCallWitness> StackCalls => stackCalls;
}
