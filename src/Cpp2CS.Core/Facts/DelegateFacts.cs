using Cpp2CS.Model;
using System.Reflection;

namespace Cpp2CS.Facts;

/// <summary>委托身份只取元数据继承链和精确签名；不能用类型名或规范共享入口代替具体类型。</summary>
public static class DelegateFacts
{
    /// <summary>ECMA-335 II.14.6：委托的运行时成员由 CLI 实现，声明不得带普通 CIL 方法体。</summary>
    public static bool IsRuntimeMethod(MethodDef method)
    {
        static bool Core(TypeRef type, string name) => type is DefinitionRef
            { Definition: { Assembly: "mscorlib.dll", Namespace: "System", DeclaringType: null } definition, Arguments.Count: 0 } && definition.Name == name;
        static bool Runtime(MethodDef m) => !m.IsStatic && !m.IsAbstract && m.GenericParameters.Count == 0
            && (m.Attributes & MethodAttributes.PinvokeImpl) == 0
            && (m.ImplAttributes & (MethodImplAttributes.CodeTypeMask | MethodImplAttributes.ManagedMask)) == MethodImplAttributes.Runtime;
        var owner = method.Owner;
        if ((owner.Attributes & TypeAttributes.Sealed) == 0 || owner.IsValueType || owner.BaseType is null
            || !Core(owner.BaseType, "MulticastDelegate") || !Runtime(method)
            || owner.Methods.Where(m => m.Name == "Invoke").ToArray() is not [var invoke] || !Runtime(invoke) || !invoke.IsVirtual) return false;
        var parameters = method.Parameters.Select(p => p.Type).ToArray();
        var invoked = invoke.Parameters.Select(p => p.Type).ToArray();
        return method.Name switch
        {
            ".ctor" => parameters is [var target, var pointer] && Core(target, "Object") && Core(pointer, "IntPtr")
                && Core(method.ReturnType, "Void") && (method.Attributes & (MethodAttributes.SpecialName | MethodAttributes.RTSpecialName))
                    == (MethodAttributes.SpecialName | MethodAttributes.RTSpecialName),
            "Invoke" => ReferenceEquals(method, invoke),
            "BeginInvoke" => method.IsVirtual && Core(method.ReturnType, "IAsyncResult") && parameters.Length == invoked.Length + 2
                && parameters.Take(invoked.Length).SequenceEqual(invoked) && Core(parameters[^2], "AsyncCallback") && Core(parameters[^1], "Object"),
            "EndInvoke" => method.IsVirtual && method.ReturnType.Equals(invoke.ReturnType) && parameters.Length > 0
                && Core(parameters[^1], "IAsyncResult") && parameters[..^1].SequenceEqual(invoked.Where(p => p is ByRefRef)),
            _ => false,
        };
    }

    public static bool IsDelegate(TypeRef type)
    {
        for (TypeRef? current = type; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition.FullName == "System.MulticastDelegate" && d.Definition.Assembly == "mscorlib.dll") return true;
        return false;
    }

    public static MethodRef? Invoke(DefinitionRef type) => IsDelegate(type)
        && type.Definition.Methods.Where(m => m.Name == "Invoke" && !m.IsStatic).ToArray() is [var method] ? new(method, type.Arguments, []) : null;

    public static MethodRef? Constructor(DefinitionRef type) => IsDelegate(type)
        && type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 2
            && m.Parameters[0].Type is DefinitionRef { Definition.FullName: "System.Object" }
            && m.Parameters[1].Type is DefinitionRef { Definition.FullName: "System.IntPtr" }).ToArray() is [var method] ? new(method, type.Arguments, []) : null;
}
