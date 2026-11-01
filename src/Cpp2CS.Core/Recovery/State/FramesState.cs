using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class FramesState : IStatementKeyed
{
    internal readonly Dictionary<long, RecoveryHole> frameHoles = new();
    internal readonly Dictionary<Stmt, ManagedStatement[]> frameCopies = new(StatementIdentity.Instance);
    internal readonly List<FrameRegion> frameRegions = [];
    internal FrameRegion[] discoveryFrames = [];
    internal readonly HashSet<long> conflictingFrames = [];
    internal readonly Dictionary<FrameRegion, HashSet<Stmt>> frameLives = [];
    internal readonly Dictionary<Stmt, ManagedStatement[]> frameInitializers = new(StatementIdentity.Instance);
    // ---------- 装箱子域 ----------
    internal readonly Dictionary<Variable, LocalValue> mergedBoxValues = [];
    internal readonly Dictionary<Store, LocalValue> boxArgumentStores = new(StatementIdentity.Instance);
    /// <summary>装箱调用 → 写入被装箱栈槽的值。</summary>
    internal readonly Dictionary<Call, Expr> boxed = new(StatementIdentity.Instance);
    internal readonly Dictionary<Store, LocalValue> stackArgumentStores = new(StatementIdentity.Instance);
    internal readonly Dictionary<(ulong Site, int Parameter), ManagedValue> stackArgumentValues = [];
    internal readonly Dictionary<ulong, (long Offset, int Size)> callStackAreas = [];
    internal readonly Dictionary<Call, StackEnum> stackEnums = new(StatementIdentity.Instance);
    internal readonly HashSet<Stmt> stackEnumStorage = new(StatementIdentity.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(boxArgumentStores, previous, replacement);
        StatementKeys.Replace(boxed, previous, replacement);
        StatementKeys.Replace(frameCopies, previous, replacement);
        StatementKeys.Replace(frameInitializers, previous, replacement);
        StatementKeys.Replace(stackArgumentStores, previous, replacement);
        StatementKeys.Replace(stackEnums, previous, replacement);
        StatementKeys.Replace(stackEnumStorage, previous, replacement);
        foreach (var live in frameLives.Values) StatementKeys.Replace(live, previous, replacement);
    }
}
