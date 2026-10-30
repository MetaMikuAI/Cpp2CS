using System.Reflection;

namespace Cpp2CS.Extensions.Closure;

/// <summary>F9b：元数据中的自动属性证据。名称只用于关联，字段和所有现存访问器还必须有编译器特性。</summary>
public static class AutoPropertyAccessor
{
    public const string CompilerGenerated = "System.Runtime.CompilerServices.CompilerGeneratedAttribute";
    public static bool Generated(IReadOnlyList<CustomAttributeDef> attributes) => attributes.Any(a =>
        a.Constructor.Owner.FullName == CompilerGenerated && a.Constructor.Owner.Assembly == "mscorlib.dll"
        && a.Constructor.Name == ".ctor" && a.Constructor.Parameters.Count == 0 && a.Arguments.Count == 0);
    public static bool BackingName(string name) => name.StartsWith('<') && name.EndsWith(">k__BackingField", StringComparison.Ordinal);
    public static PropertyDef? Property(FieldDef field) => BackingName(field.Name)
        && field.Owner.Properties.Where(p => p.Name == field.Name[1..^">k__BackingField".Length]).ToArray() is [var property] ? property : null;

    public static string? Problem(FieldDef field, ManagedTypes types)
    {
        if (!BackingName(field.Name)) return "不是后备字段命名";
        if (!Generated(field.CustomAttributes)) return "字段缺少CompilerGenerated";
        if (Property(field) is not { } property) return "属性关联不唯一或缺失";
        if (field.Owner.Fields.Count(f => f.Name == field.Name) != 1) return "字段不唯一";
        if ((field.Attributes & FieldAttributes.FieldAccessMask) != FieldAttributes.Private) return "字段非私有";
        var accessors = new[] { (Method: property.Getter, Write: false), (Method: property.Setter, Write: true) }.Where(a => a.Method is not null).ToArray();
        if (accessors.Length == 0) return "没有访问器定义";
        if (accessors.Any(a => !Generated(a.Method!.CustomAttributes))) return "访问器缺少CompilerGenerated";
        if (accessors.Any(a => a.Method!.Owner != field.Owner || a.Method.IsStatic != field.IsStatic || a.Method.GenericParameters.Count != 0
            || a.Method.IsAbstract || (a.Method.Attributes & MethodAttributes.PinvokeImpl) != 0
            || a.Method.ImplAttributes != MethodImplAttributes.IL
            || (a.Write ? a.Method.Parameters.Count != 1 || !a.Method.Parameters[0].Type.Equals(field.Type) || !ManagedTypes.IsVoid(a.Method.ReturnType)
                : a.Method.Parameters.Count != 0 || !a.Method.ReturnType.Equals(field.Type)))) return "签名或静态性不符";
        if (field.Owner.GenericParameters.Count != 0) return "泛型声明类型";
        if (field.Owner.IsValueType && !field.IsStatic) return "值类型实例";
        if (accessors.Any(a => a.Method!.IsVirtual && (a.Method.Attributes & MethodAttributes.Final) == 0)) return "可重写虚访问器";
        if (field.IsThreadStatic || field.Offset < 0) return "字段布局不支持";
        if (types.Bits(field.Type) <= 0 || field.Type is ByRefRef) return "字段类型不支持";
        if (property.Setter is not null && (field.Attributes & FieldAttributes.InitOnly) != 0) return "只读字段写访问器";
        return null;
    }

    public static Dictionary<MethodDef, FieldAccessor> Candidates(ManagedTypes types)
    {
        var output = new Dictionary<MethodDef, FieldAccessor>();
        foreach (var field in types.Model.Fields.Where(f => Problem(f, types) is null))
        {
            var property = Property(field)!;
            foreach (var (method, write) in new[] { (property.Getter, false), (property.Setter, true) })
                if (method is not null)
                    output.Add(method, new(new(method, [], []), new(field, new DefinitionRef(field.Owner, [])), field.Type, types.Bits(field.Type), write)
                    { LanguageDefined = true });
        }
        return output;
    }

    public static ManagedBody Synthesize(FieldAccessor accessor)
    {
        var method = accessor.Method;
        var address = method.Method.Address;
        // C# §15.7.4 的自动访问器只读/写后备字段。Unity 2022.3 的 C# 9 没有 field 半自动属性。
        ManagedValue storage = method.Method.IsStatic ? new StaticFieldValue(accessor.Field, accessor.ValueType, accessor.Width)
            : new FieldValue(new ArgumentValue(-1, method.DeclaringType, 64), accessor.Field, accessor.ValueType, accessor.Width);
        return new(method, [new(address, accessor.Write
            ? [new ManagedStore(address, storage, new ArgumentValue(0, accessor.ValueType, accessor.Width)), new ManagedReturn(address, null)]
            : [new ManagedReturn(address, storage)])]);
    }
}
