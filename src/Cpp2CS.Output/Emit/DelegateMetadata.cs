namespace Cpp2CS.Output;

/// <summary>从元数据继承链与签名选择委托构造函数。</summary>
internal static class DelegateMetadata
{
    public static bool IsDelegate(TypeRef type)
    {
        for (TypeRef? current = type; current is DefinitionRef d; current = d.Definition.BaseType?.Substitute(d.Arguments, []))
            if (d.Definition.FullName == "System.MulticastDelegate" && d.Definition.Assembly == "mscorlib.dll") return true;
        return false;
    }

    public static MethodRef? Constructor(DefinitionRef type) => IsDelegate(type)
        && type.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.Parameters.Count == 2
            && m.Parameters[0].Type is DefinitionRef { Definition.FullName: "System.Object" }
            && m.Parameters[1].Type is DefinitionRef { Definition.FullName: "System.IntPtr" }).ToArray() is [var method] ? new(method, type.Arguments, []) : null;
}
