
namespace Cpp2CS.Recovery;

internal static class FrameInitialization
{
    internal static IEnumerable<ulong> Uninitialized(ManagedBody body, IReadOnlySet<ManagedValue> all,
        Func<ManagedValue, HashSet<ManagedValue>> under) => DefiniteInitialization.Uninitialized(body, all, under);
}
