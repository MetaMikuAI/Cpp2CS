using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>
/// 托管成员与类型的访问权限。原生代码内联了别的类型的访问器时，恢复出的直接访问可能越权；
/// 内联的也可能是内部类型的成员（如 Array.Empty&lt;T&gt;() 内联成 System.EmptyArray&lt;T&gt;.Value），所以成员的声明类型本身也要可访问。
/// </summary>
public static class ManagedAccess
{
    public static bool Field(ManagedTypes types, TypeDef caller, FieldRef field, TypeRef? receiver) =>
        Type(types, caller, field.DeclaringType)
        && Allowed(types, caller, field.Field.Owner, field.DeclaringType, (int)(field.Field.Attributes & FieldAttributes.FieldAccessMask), receiver);

    public static bool Method(ManagedTypes types, TypeDef caller, MethodRef method, TypeRef? receiver) =>
        Type(types, caller, method.DeclaringType) && method.MethodArguments.All(a => Type(types, caller, a))
        && Allowed(types, caller, method.Method.Owner, method.DeclaringType, (int)(method.Method.Attributes & MethodAttributes.MemberAccessMask), receiver);

    /// <summary>
    /// 类型能否在 caller 中按名引用（C# 的规则）：顶层类型须为 public 或在同一程序集；嵌套类型按成员规则判定，并要求外层类型可访问；
    /// 泛型实参、数组与指针元素同样要可访问。骨架不处理 InternalsVisibleTo，按不可见计。
    /// </summary>
    public static bool Type(ManagedTypes types, TypeDef caller, TypeRef type) => type switch
    {
        DefinitionRef d => Definition(types, caller, d) && d.Arguments.All(a => Type(types, caller, a)),
        ArrayRef a => Type(types, caller, a.Element),
        PointerRef p => Type(types, caller, p.Element),
        ByRefRef r => Type(types, caller, r.Element),
        _ => true,
    };

    private static bool Definition(ManagedTypes types, TypeDef caller, DefinitionRef type)
    {
        var visibility = type.Definition.Attributes & TypeAttributes.VisibilityMask;
        if (type.Definition.DeclaringType is not { } outer)
            return visibility == TypeAttributes.Public || type.Definition.Assembly == caller.Assembly;
        // 嵌套类型的实参按 CLR 规则以外层类型的实参开头
        var outerType = new DefinitionRef(outer, type.Arguments.Take(outer.GenericParameters.Count).ToArray());
        var access = visibility switch
        {
            TypeAttributes.NestedPublic => 6, TypeAttributes.NestedPrivate => 1, TypeAttributes.NestedFamANDAssem => 2,
            TypeAttributes.NestedAssembly => 3, TypeAttributes.NestedFamily => 4, TypeAttributes.NestedFamORAssem => 5,
            _ => 0,
        };
        return Definition(types, caller, outerType) && Allowed(types, caller, outer, outerType, access, null);
    }

    // FieldAccessMask 与 MemberAccessMask 的 0..6 取值相同。Family 同时限制访问上下文与接收者类型。
    private static bool Allowed(ManagedTypes types, TypeDef caller, TypeDef owner, TypeRef declaringType, int access, TypeRef? receiver)
    {
        var sameAssembly = owner.Assembly == caller.Assembly;
        var privateAccess = false;
        var familyAccess = false;
        for (var context = caller; context is not null; context = context.DeclaringType)
        {
            privateAccess |= context == owner;
            var contextType = new DefinitionRef(context, []);
            var receiverType = receiver is ByRefRef byRef ? byRef.Element : receiver;
            familyAccess |= types.IsAssignable(contextType, declaringType)
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
