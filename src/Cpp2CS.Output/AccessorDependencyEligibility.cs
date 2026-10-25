using Mono.Cecil;

namespace Cpp2CS.Output;

/// <summary>依赖也必须能通过既有 C# 编译门槛；不修补缺失的属性元数据，不按类型名称设置例外。</summary>
public static class AccessorDependencyEligibility
{
    public static IEnumerable<MethodDefinition> UnassociatedImplementations(TypeDefinition type)
    {
        var associated = type.Properties.SelectMany(p => new[] { p.GetMethod, p.SetMethod }).OfType<MethodDefinition>().ToHashSet();
        foreach (var method in type.Methods.Where(m => !associated.Contains(m)))
            if (method.Overrides.Any(o => o.Resolve() is { } target && target.DeclaringType.Properties.Any(p => p.GetMethod == target || p.SetMethod == target)))
                yield return method;
    }

    public static string? Problem(TypeDefinition type)
    {
        while (type.DeclaringType is { } outer) type = outer;
        IEnumerable<TypeDefinition> Nested(TypeDefinition t) => new[] { t }.Concat(t.NestedTypes.SelectMany(Nested));
        return Nested(type).SelectMany(UnassociatedImplementations).FirstOrDefault() is { } method
            ? $"依赖骨架 显式接口访问器 {method.FullName} 缺少属性关联（C# CS0683）" : null;
    }
}
