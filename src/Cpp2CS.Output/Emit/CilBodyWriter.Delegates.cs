using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

internal sealed partial class CilBodyWriter
{
    private void EmitDelegate(DelegateValue value)
    {
        Value(value.Target);
        if (value.Binding == DelegateBinding.VirtualInstance)
        {
            il.Emit(OpCodes.Dup);
            il.Emit(OpCodes.Ldvirtftn, MethodReference(value.Method));
        }
        else il.Emit(OpCodes.Ldftn, MethodReference(value.Method));
        il.Emit(OpCodes.Newobj, MethodReference(DelegateMetadata.Constructor(value.DelegateType)!));
    }
}
