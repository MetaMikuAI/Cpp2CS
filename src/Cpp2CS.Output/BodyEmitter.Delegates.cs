using Cpp2CS.Facts;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

public sealed partial class BodyEmitter
{
    private string? DelegateProblem(DelegateValue value)
    {
        if (DelegateFacts.Constructor(value.DelegateType) is not { } constructor) return "委托 缺少标准构造";
        if (!CanAccess(constructor, value.Type)) return $"访问权限 委托构造 {constructor}";
        if (!CanAccess(value.Method, value.Binding == DelegateBinding.Static ? null : value.Target.Type)) return $"访问权限 委托方法 {value.Method}";
        // 直接 Method 符号不能换成 ldvirtftn。非 final 的虚方法只有接收者类型封闭时才采用此序列。
        if (value.Binding != DelegateBinding.VirtualInstance && value.Method.Method.IsVirtual && (value.Method.Method.Attributes & System.Reflection.MethodAttributes.Final) == 0
            && value.Target.Type is Cpp2CS.Model.DefinitionRef d && (d.Definition.Attributes & System.Reflection.TypeAttributes.Sealed) == 0)
            return "委托 直接虚方法绑定的验证条件未证明";
        return null;
    }

    private void EmitDelegate(DelegateValue value)
    {
        Value(value.Target);
        if (value.Binding == DelegateBinding.VirtualInstance)
        {
            il.Emit(OpCodes.Dup);
            il.Emit(OpCodes.Ldvirtftn, MethodReference(value.Method));
        }
        else il.Emit(OpCodes.Ldftn, MethodReference(value.Method));
        il.Emit(OpCodes.Newobj, MethodReference(DelegateFacts.Constructor(value.DelegateType)!));
    }
}
