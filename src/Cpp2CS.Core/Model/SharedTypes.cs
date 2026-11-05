
namespace Cpp2CS.Model;

public static class SharedTypes
{
    public static bool IsFullyShared(TypeRef type) => type switch
    {
        DefinitionRef d => d.Definition.Namespace == "Unity.IL2CPP.Metadata" && d.Definition.Name.StartsWith("__Il2CppFullyShared", StringComparison.Ordinal)
            || d.Arguments.Any(IsFullyShared),
        ArrayRef a => IsFullyShared(a.Element),
        PointerRef p => IsFullyShared(p.Element),
        ByRefRef r => IsFullyShared(r.Element),
        _ => false,
    };

    /// <summary>
    /// 可变大小的存储：完全共享的类型参数，或实例字段（沿值类型递归）含这种类型的泛型值类型。
    /// 布局只有运行时知道，codegen 经地址传递，返回缓冲区在显式参数之后、MethodInfo 之前。
    /// 只含引用、数组或指针的实例（实参虽是占位类型）布局固定，仍按普通结构传递。
    /// </summary>
    public static bool IsVariableSized(TypeRef type) => type switch
    {
        GenericParameterRef { NativeShared: true } => true,
        DefinitionRef { Definition: { Namespace: "Unity.IL2CPP.Metadata", Name: "__Il2CppFullySharedGenericType" or "__Il2CppFullySharedGenericStructType" } } => true,
        DefinitionRef { Arguments.Count: > 0, Definition.IsValueType: true } d =>
            d.Definition.Fields.Any(f => !f.IsStatic && IsVariableSized(f.Type.Substitute(d.Arguments, []))),
        _ => false,
    };
}
