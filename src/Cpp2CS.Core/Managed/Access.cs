using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>托管成员的访问权限。原生内联不改变恢复后 CIL/C# 所需的权限。</summary>
public static class ManagedAccess
{
    public static bool Field(ManagedTypes types, TypeDef caller, FieldRef field, TypeRef receiver) =>
        Allowed(types, caller, field.Field.Owner, (int)(field.Field.Attributes & FieldAttributes.FieldAccessMask), receiver);

    public static bool Method(ManagedTypes types, TypeDef caller, MethodRef method, TypeRef? receiver) =>
        Allowed(types, caller, method.Method.Owner, (int)(method.Method.Attributes & MethodAttributes.MemberAccessMask), receiver);

    // FieldAccessMask 与 MemberAccessMask 的 0..6 取值相同。Family 同时限制访问上下文与接收者类型。
    private static bool Allowed(ManagedTypes types, TypeDef caller, TypeDef owner, int access, TypeRef? receiver)
    {
        var sameAssembly = owner.Assembly == caller.Assembly;
        var privateAccess = false;
        var familyAccess = false;
        for (var context = caller; context is not null; context = context.DeclaringType)
        {
            privateAccess |= context == owner;
            var contextType = new DefinitionRef(context, []);
            var receiverType = receiver is ByRefRef byRef ? byRef.Element : receiver;
            familyAccess |= types.IsAssignable(contextType, new DefinitionRef(owner, []))
                && (receiverType is null || types.IsAssignable(receiverType, contextType));
        }
        return access switch
        {
            6 => true, 1 => privateAccess, 2 => familyAccess && sameAssembly,
            3 => sameAssembly, 4 => familyAccess, 5 => familyAccess || sameAssembly,
            _ => false,
        };
    }
}
