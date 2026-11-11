using Cpp2CS.Model;
namespace Cpp2CS.Tests.Execution;

/// <summary>解释器的紧密字段存储。只用于托管值，不推断目标运行时布局。</summary>
internal sealed class ManagedStorage(Action<TypeDef> prepare) : ITypeLayouts
{
    private readonly Dictionary<DefinitionRef, TypeLayout> layouts = [];
    private readonly HashSet<DefinitionRef> active = [];
    public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => SizeAndAlignment(type);
    public (int Size, int Alignment) SizeAndAlignment(TypeRef type)
    {
        if (type.ContainsGenericParameter()) throw new Unsupported($"开放泛型布局 {type}");
        if (ManagedTypes.IsReferenceType(type) || type is PointerRef or ByRefRef) return (8, 1);
        type = ManagedTypes.Underlying(type);
        var size = ManagedTypes.PrimitiveName(type) switch { "Void" => 0, "Boolean" or "Byte" or "SByte" => 1,
            "Char" or "Int16" or "UInt16" => 2, "Int32" or "UInt32" or "Single" => 4,
            "Int64" or "UInt64" or "Double" or "IntPtr" or "UIntPtr" => 8, _ => -1 };
        if (size >= 0) return (size, 1);
        if (type is DefinitionRef d) return (Of(d)!.ValueSize, 1);
        throw new Unsupported($"没有托管存储定义：{type}");
    }
    public TypeLayout? Of(DefinitionRef type)
    {
        if (layouts.TryGetValue(type, out var found)) return found;
        prepare(type.Definition);
        if (!active.Add(type)) throw new Unsupported($"递归值布局 {type}");
        if ((type.Definition.Attributes & System.Reflection.TypeAttributes.ExplicitLayout) != 0) throw new Unsupported($"显式重叠布局 {type}");
        var instance = StorageLayout.ObjectHeaderSize;
        if (!type.Definition.IsValueType && type.Definition.BaseType?.Substitute(type.Arguments, []) is DefinitionRef parent)
            instance = Of(parent)!.InstanceSize;
        var statics = 0;
        var fields = new List<FieldSlot>(); var staticFields = new List<FieldSlot>();
        var primitive = ManagedTypes.PrimitiveName(type);
        if (primitive is not null && primitive != "Void") instance += SizeAndAlignment(type).Size;
        else foreach (var field in type.Definition.Fields.Where(f => !f.IsStatic))
        {
            var concrete = field.Type.Substitute(type.Arguments, []);
            fields.Add(new(field, concrete, instance));
            instance += SizeAndAlignment(concrete).Size;
        }
        if (type.Definition.IsValueType && instance == StorageLayout.ObjectHeaderSize) instance++;
        TypeLayout Snapshot() => new() { Type = type, ObjectHeaderSize = StorageLayout.ObjectHeaderSize, InstanceSize = instance,
            ActualSize = instance, MinimumAlignment = 1, HasReferences = fields.Any(f => ManagedTypes.IsReferenceType(f.Type)),
            Fields = fields.ToArray(), Statics = staticFields.ToArray(), StaticSize = statics, ThreadStatics = [], FromMetadata = false };
        // 实例大小先固定，静态字段随后计算，避免 S 的 static S 字段递归进入自身布局。
        layouts.Add(type, Snapshot());
        active.Remove(type);
        foreach (var field in type.Definition.Fields.Where(f => f.IsStatic && (f.Attributes & System.Reflection.FieldAttributes.Literal) == 0))
        {
            var concrete = field.Type.Substitute(type.Arguments, []);
            staticFields.Add(new(field, concrete, statics));
            statics += SizeAndAlignment(concrete).Size;
        }
        return layouts[type] = Snapshot();
    }
}
