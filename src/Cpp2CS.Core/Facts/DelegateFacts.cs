using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>委托身份只取元数据继承链和精确签名；不能用类型名或规范共享入口代替具体类型。</summary>
public static class DelegateFacts
{
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
