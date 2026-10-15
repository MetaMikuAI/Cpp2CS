using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

public sealed record ObjectAllocationPlan(MethodRef GetTypeFromHandle, MethodRef Allocate, MethodRef? Initialize);

/// <summary>普通引用对象的清零分配。数组、字符串、委托、值类型及不能实例化的类型保留专用恢复路径。</summary>
public static class ObjectAllocation
{
    public static bool Supported(ManagedTypes types, TypeRef type) => type is DefinitionRef { Definition.IsValueType: false } d
        && ManagedTypes.IsClosed(d) && !d.Definition.IsInterface
        && (d.Definition.Attributes & (TypeAttributes.Abstract | TypeAttributes.Import)) == 0
        && type != types.String && !types.IsAssignable(type, types.Delegate)
        && !(types.CorlibDefinition("System.ContextBoundObject") is { } context && types.IsAssignable(type, new DefinitionRef(context, [])));

    public static ObjectAllocationPlan? Plan(ManagedTypes types, TypeRef type, out string? problem)
    {
        problem = null;
        if (!Supported(types, type)) { problem = "对象分配类型尚未支持"; return null; }
        bool PublicStatic(MethodDef method) => method.IsStatic
            && (method.Attributes & MethodAttributes.MemberAccessMask) == MethodAttributes.Public;
        var getType = types.Type.Definition.Methods.SingleOrDefault(m => PublicStatic(m) && m.Name == "GetTypeFromHandle"
            && m.ReturnType == types.Type && m.Parameters is [{ Type: var parameter }] && parameter == types.RuntimeTypeHandle);
        var allocate = types.CorlibDefinition("System.Runtime.Serialization.FormatterServices")?.Methods.SingleOrDefault(m => PublicStatic(m)
            && m.Name == "GetUninitializedObject" && m.ReturnType == types.Object && m.Parameters is [{ Type: var parameter }] && parameter == types.Type);
        if (getType is null || allocate is null) { problem = "元数据缺少普通对象的无构造分配接口"; return null; }
        MethodRef? initialize = null;
        if (((DefinitionRef)type).Definition.Methods.Any(m => m.Name == ".cctor" && m.IsStatic))
        {
            if (ClassInitialization.Invocation(types, type, out problem) is not { } invocation) return null;
            initialize = invocation.Method;
        }
        return new(new(getType, [], []), new(allocate, [], []), initialize);
    }
}
