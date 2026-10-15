using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>具体实例上的字段位置，Offset 相对值数据起始，不修改泛型定义的偏移。</summary>
public sealed record InstanceField(FieldRef Field, TypeRef Type, int Offset);

/// <summary>值的大小、自然对齐及实例字段。IsInstantiated 表示按实参推导，尚非运行时测量。</summary>
public sealed record ValueLayout(int Size, int Alignment, IReadOnlyList<InstanceField> Fields, bool IsInstantiated);

/// <summary>
/// 64 位 IL2CPP 的自然值布局。非泛型结构逐字段核对元数据偏移和总大小；泛型结构先代入实参再计算。
/// 未知类型、显式布局、自定义 packing/大小和循环值布局不推测。
/// </summary>
public sealed class ValueLayouts
{
    private readonly Dictionary<TypeRef, ValueLayout?> cache = new();
    private readonly HashSet<TypeRef> active = [];

    public ValueLayout? Get(TypeRef type)
    {
        if (cache.TryGetValue(type, out var known)) return known;
        if (!active.Add(type)) return null;
        var result = Compute(type);
        active.Remove(type);
        return cache[type] = result;
    }

    private ValueLayout? Compute(TypeRef type)
    {
        if (type is PointerRef or ByRefRef or ArrayRef or PrimitiveRef { Name: "nint" }
            || type is DefinitionRef { Definition.IsValueType: false }) return Scalar(8);
        if (type is not DefinitionRef d) return null;
        if (d.Definition.IsEnum)
            return Get(d.Definition.Fields.First(f => !f.IsStatic).Type.Substitute(d.Arguments, []));
        var primitive = ManagedTypes.PrimitiveName(type) switch
        {
            "Boolean" or "Byte" or "SByte" => 1,
            "Char" or "Int16" or "UInt16" => 2,
            "Int32" or "UInt32" or "Single" => 4,
            "Int64" or "UInt64" or "Double" or "IntPtr" or "UIntPtr" => 8,
            _ => 0,
        };
        if (primitive != 0) return Scalar(primitive);
        var definition = d.Definition;
        if (definition.PackingSize != 0 || definition.ClassSizeIsDefault != true
            || (definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout
            || d.Arguments.Count != definition.GenericParameters.Count) return null;
        var fields = new List<InstanceField>();
        int end = 0, alignment = 1;
        foreach (var field in definition.Fields.Where(f => !f.IsStatic))
        {
            var fieldType = field.Type.Substitute(d.Arguments, []);
            if (Get(fieldType) is not { } layout) return null;
            var offset = Align(end, layout.Alignment);
            if (d.Arguments.Count == 0 && field.Offset != offset) return null;
            fields.Add(new InstanceField(new FieldRef(field, d), fieldType, offset));
            end = checked(offset + layout.Size);
            alignment = Math.Max(alignment, layout.Alignment);
        }
        // 空结构的实际占用没有字段证据，不从空字段列表推断。
        if (fields.Count == 0) return null;
        var size = Align(end, alignment);
        if (d.Arguments.Count == 0 && definition.Size != size) return null;
        return new ValueLayout(size, alignment, fields, d.Arguments.Count > 0);
    }

    private static ValueLayout Scalar(int size) => new(size, size, [], false);
    private static int Align(int value, int alignment) => checked(value + alignment - 1) & -alignment;
}
