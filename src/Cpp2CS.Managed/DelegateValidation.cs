using System.Reflection;

namespace Cpp2CS.Managed;

/// <summary>委托直接绑定虚方法的 CLI 验证条件，供恢复与输出共用。</summary>
public static class DelegateValidation
{
    public static bool ThisUnmodified(ManagedBody body) => !body.Method.Method.IsStatic
        && !body.Blocks.SelectMany(b => b.Statements).Any(statement =>
            statement is ManagedStore { Target: ArgumentValue { Index: -1 } }
            || ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk)
                .Any(v => v is AddressValue { Target: ArgumentValue { Index: -1 } }));

    public static bool DirectBindingAllowed(DelegateValue value, MethodRef context, bool thisUnmodified) =>
        value.Binding == DelegateBinding.VirtualInstance || !value.Method.Method.IsVirtual
        || (value.Method.Method.Attributes & MethodAttributes.Final) != 0
        || value.Target.Type is not DefinitionRef type || (type.Definition.Attributes & TypeAttributes.Sealed) != 0
        || value.Target is ArgumentValue { Index: -1 } && thisUnmodified && !context.Method.Owner.IsValueType;
}
