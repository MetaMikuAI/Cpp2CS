using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>下降阶段可读取的证据；表的写入仅由分析与机器 pass 持有。</summary>
internal sealed class RecoveryEvidence(MethodState state)
{
    public CallsView Calls { get; } = new(state.Calls);
    internal sealed class CallsView(CallsState state)
    {
        public IReadOnlySet<Call> cleanupCalls => state.cleanupCalls;
        public IReadOnlySet<ulong> inlineCleanupSites => state.inlineCleanupSites;
        public IReadOnlyDictionary<Call, MethodRef> nativeImports => state.nativeImports;
        public IReadOnlyDictionary<IndirectJump, Expr> switchIndices => state.switchIndices;
    }
    public ConstructionView Construction { get; } = new(state.Construction);
    internal sealed class ConstructionView(ConstructionState state)
    {
        public IReadOnlyDictionary<Call, DefinitionRef> delegateCreations => state.delegateCreations;
        public IReadOnlyDictionary<Store, LocalValue> boxArgumentStores => state.boxArgumentStores;
        public IReadOnlyDictionary<Variable, LocalValue> mergedBoxValues => state.mergedBoxValues;
        public IReadOnlyDictionary<Call, Variable> constructed => state.constructed;
    }
    public SignatureView Signature { get; } = new(state.Signature);
    internal sealed class SignatureView(SignatureState state)
    {
        public TypeRef returnType => state.returnType;
        public LocalValue? ownReturnBuffer => state.ownReturnBuffer;
    }
    public LoweringView Lowering { get; } = new(state.Lowering);
    internal sealed class LoweringView(LoweringState state)
    {
        public IReadOnlySet<Variable> inlined => state.inlined;
    }
    public ExceptionsView Exceptions { get; } = new(state.Exceptions);
    internal sealed class ExceptionsView(ExceptionsState state)
    {
        public IReadOnlyDictionary<Call, TypeRef> exceptionTypeTargets => state.exceptionTypeTargets;
    }
    public RuntimeView Runtime { get; } = new(state.Runtime);
    internal sealed class RuntimeView(RuntimeState state)
    {
        public IReadOnlyDictionary<Call, Use> typeChecks => state.typeChecks;
    }
    public FramesView Frames { get; } = new(state.Frames);
    internal sealed class FramesView(FramesState state)
    {
        public IReadOnlyDictionary<Stmt, ManagedStatement[]> frameCopies => state.frameCopies;
        public IReadOnlyDictionary<Stmt, ManagedStatement[]> frameInitializers => state.frameInitializers;
        public IReadOnlyList<FrameRegion> frameRegions => state.frameRegions;
        public IReadOnlyDictionary<Store, LocalValue> stackArgumentStores => state.stackArgumentStores;
        public IReadOnlyDictionary<(ulong Site, int Parameter), ManagedValue> stackArgumentValues => state.stackArgumentValues;
    }
    public StructsView Structs { get; } = new(state.Structs);
    internal sealed class StructsView(StructsState state)
    {
        public IReadOnlyDictionary<Variable, Expr> fragmentDefinitions => state.fragmentDefinitions;
    }
    public ArraysView Arrays { get; } = new(state.Arrays);
    internal sealed class ArraysView(ArraysState state)
    {
        public IReadOnlyDictionary<(Call Call, int Parameter), ArraySpan> arraySpans => state.arraySpans;
    }
}
