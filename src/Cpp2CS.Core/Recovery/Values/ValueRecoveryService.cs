using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>下降与表达式定型共用的值恢复入口；方法内缓存由恢复器持有。</summary>
internal sealed class ValueRecoveryService(RecoveryScope host)
{
    public MethodRef? PrecedingStart(Call call) => host.PrecedingStart(call);
    public IEnumerable<(FieldRef[] Path, TypeRef Type, int Offset)> StructPaths(TypeRef type, int offset = 0, FieldRef[]? path = null) => host.StructPaths(type, offset, path);
    public RecoveryResult<ManagedValue> StructAddress(Expr expression, TypeRef expected) => host.StructAddress(expression, expected);
    public ManagedValue PathValue(ManagedValue root, IReadOnlyList<FieldRef> path) => host.PathValue(root, path);
    public RecoveryResult<ManagedValue> RecoverAs(Expr e, TypeRef target, ulong address) => host.RecoverAs(e, target, address);
    public RecoveryFailure? CreateDelegate(Call call, List<ManagedStatement> output) => host.CreateDelegate(call, output);
    public RecoveryResult<LocalValue> Local(Variable v) => host.Local(v);
    public bool MissingInput(Expr expression) => host.MissingInput(expression);
    public bool DirectInputProof(Call call, MethodRef callee, bool receiver = false) => host.DirectInputProof(call, callee, receiver);
    public bool UnusedParameter(Call call, Storage register) => host.UnusedParameter(call, register);
    public RecoveryResult<ManagedValue> Recover(Expr e, TypeRef? hint) => host.Recover(e, hint);
    public RecoveryResult<ManagedValue> Coerce(ManagedValue value, TypeRef target, ulong address) => host.Coerce(value, target, address);
    public RecoveryResult<ManagedEdge> Edge(Block from, int successor, ulong target) => host.Edge(from, successor, target);
    public RecoveryResult<ManagedValue> Index(Expr index) => host.Index(index);
    public RecoveryFailure? Assign(ulong address, Variable target, Func<RecoveryResult<ManagedValue>> value, List<ManagedStatement> output) => host.Assign(address, target, value, output);
    public bool FrameZero(Expr expression, HashSet<Variable>? active = null) => host.FrameZero(expression, active);
    public (FrameRegion Region, long Offset)? FrameAccess(Expr address) => host.FrameAccess(address);
    public RecoveryResult<CopyRange[]> CopyRanges(Expr address, int width) => host.CopyRanges(address, width);
    public ManagedValue? WholeStructAt(CopyRange range, int width) => host.WholeStructAt(range, width);
    public RecoveryResult<ManagedValue> FrameLocation(FrameRegion region, long offset, int width) => host.FrameLocation(region, offset, width);
    public RecoveryResult<ManagedValue> SharedValue(Expr address, TypeRef type) => host.SharedValue(address, type);
    public MethodRef? Resolve(Call call) => host.Resolve(call);
    public Expr Expand(Expr e) => host.Expand(e);
    public LocalValue StructLocal(TypeRef type, int width) => host.StructLocal(type, width);
    public RecoveryResult<Fragment?> FragmentVariable(Variable variable, int width) => host.FragmentVariable(variable, width);
    public RecoveryResult<ManagedValue> Slice(ManagedValue value, int low, int width) => host.Slice(value, low, width);
    public TypeRef? TypeOfAddressBase(Expr e) => host.TypeOfAddressBase(e);
    public Expr AddressExpression(Expr expression) => host.AddressExpression(expression);
    public bool IndirectStruct(AbiValue value) => host.IndirectStruct(value);
    public LocalValue CallStructLocal(Call call, TypeRef type) => host.CallStructLocal(call, type);
    public bool RegisterStruct(AbiValue value) => host.RegisterStruct(value);
    public RecoveryResult<ManagedValue> Compose(AbiValue value, Func<AbiPiece, RecoveryResult<Expr>> expression) => host.Compose(value, expression);
    public RecoveryResult<ManagedValue> Location(Expr expression, int width) => host.Location(expression, width);
    public NewObjectValue? ThrowingConstructor(MethodRef method, ulong entry) => host.owner.ThrowingConstructor(method, entry);
}
