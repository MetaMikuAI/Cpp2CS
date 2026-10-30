using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class FramesState : IStatementKeyed
{
    internal readonly Dictionary<long, RecoveryHole> frameHoles = new();
    internal readonly Dictionary<Stmt, ManagedStatement[]> frameCopies = new(ReferenceEqualityComparer.Instance);
    internal readonly List<FrameRegion> frameRegions = [];
    internal FrameRegion[] discoveryFrames = [];
    internal readonly HashSet<long> conflictingFrames = [];
    internal readonly Dictionary<FrameRegion, HashSet<Stmt>> frameLives = [];
    internal readonly Dictionary<Stmt, ManagedStatement[]> frameInitializers = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<ulong, LocalValue> sharedBuffers = [];
    internal readonly Dictionary<Store, LocalValue> stackArgumentStores = [];
    internal readonly Dictionary<(ulong Site, int Parameter), ManagedValue> stackArgumentValues = [];
    internal readonly Dictionary<ulong, (long Offset, int Size)> callStackAreas = [];
    internal readonly Dictionary<Call, StackEnum> stackEnums = new(ReferenceEqualityComparer.Instance);
    internal readonly HashSet<Stmt> stackEnumStorage = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(frameCopies, previous, replacement);
        StatementKeys.Replace(frameInitializers, previous, replacement);
        StatementKeys.Replace(stackArgumentStores, previous, replacement);
        StatementKeys.Replace(stackEnums, previous, replacement);
        StatementKeys.Replace(stackEnumStorage, previous, replacement);
        foreach (var live in frameLives.Values) StatementKeys.Replace(live, previous, replacement);
    }
}
