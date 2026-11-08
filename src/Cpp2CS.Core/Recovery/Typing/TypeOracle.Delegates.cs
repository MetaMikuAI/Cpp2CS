using Cpp2CS.Ir;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

public abstract record DelegateTarget;
public sealed record BoundDelegateTarget(MethodRef Method, DelegateBinding Binding) : DelegateTarget;
public sealed record SelectedDelegateTarget(Sym Condition, DelegateTarget True, DelegateTarget False) : DelegateTarget;

public sealed partial class TypeOracle
{
    /// <summary>委托绑定的目标及选择条件；每个分支都必须有直接方法或虚表槽的证据。</summary>
    public DelegateTarget? DelegateTargetOf(Sym pointer, Sym receiver)
    {
        pointer = SymTable.Resolve(pointer);
        if (pointer is EntitySym { Symbol: { Kind: SymbolKind.Method, Value: MethodRef method } })
            // 接口方法没有自己的代码，委托指针只能来自接口分发，等价于对接收者的虚绑定。
            return new BoundDelegateTarget(method, method.Method.IsStatic ? DelegateBinding.Static
                : method.DeclaringType is DefinitionRef { Definition.IsInterface: true } ? DelegateBinding.VirtualInstance : DelegateBinding.ClosedInstance);
        if (pointer is OpSym { Op.Kind: OperatorKind.Select, Args: [var condition, var yes, var no] }
            && DelegateTargetOf(yes, receiver) is { } taken && DelegateTargetOf(no, receiver) is { } fallthrough)
            return new SelectedDelegateTarget(condition, taken, fallthrough);
        return VirtualMethod(pointer, receiver) is { } dispatched ? new BoundDelegateTarget(dispatched, DelegateBinding.VirtualInstance) : null;
    }
}
