using Cpp2CS.Model;

namespace Cpp2CS.Managed;

public static class Boxing
{
    /// <summary>原生分配会初始化装箱对象的类型；nullable 无值时跳过，有值时初始化其内部类型。</summary>
    public static BoxInitialization? Initialization(ManagedTypes types, TypeRef type, out string? problem)
    {
        problem = null;
        if (!types.CanBox(type)) { problem = "装箱类型未知或布局尚未支持"; return null; }
        var nullable = type is DefinitionRef { Arguments: [var argument] } d && d.Definition == types.CorlibDefinition("System.Nullable") ? d : null;
        var target = nullable is not null ? nullable.Arguments[0] : type;
        if (target is not DefinitionRef definition || !definition.Definition.Methods.Any(m => m.Name == ".cctor" && m.IsStatic)) return null;
        if (ClassInitialization.Invocation(types, target, out problem) is not { } initialize) return null;
        if (nullable is null) return new(target, initialize.Method, null, null);
        var hasValue = nullable.Definition.Methods.SingleOrDefault(m => m.Name == "get_HasValue" && !m.IsStatic && m.Parameters.Count == 0 && m.ReturnType == types.Boolean);
        var getValue = nullable.Definition.Methods.SingleOrDefault(m => m.Name == "GetValueOrDefault" && !m.IsStatic && m.Parameters.Count == 0
            && m.ReturnType.Substitute(nullable.Arguments, []) == target);
        if (hasValue is null || getValue is null) { problem = "nullable 装箱缺少内部值访问方法"; return null; }
        return new(target, initialize.Method, new(hasValue, nullable.Arguments, []), new(getValue, nullable.Arguments, []));
    }
}
