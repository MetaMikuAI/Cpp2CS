using Cpp2CS.Input;
using Cpp2CS.Metadata;

namespace Cpp2CS.Semantics;

/// <summary>以元数据布局解释机器宽度，不依赖某个方法的表达式形状。</summary>
public sealed class Layouts(Catalog catalog)
{
    public int Size(string type) => type switch
    {
        "System.Boolean" or "System.Byte" or "System.SByte" => 1,
        "System.Int16" or "System.UInt16" => 2,
        "System.Int32" or "System.UInt32" or "System.Single" => 4,
        "System.Int64" or "System.UInt64" or "System.Double" => 8,
        _ when catalog.IsEnum(type) => 4,
        _ => AggregateSize(catalog.Type(type))
    };
    int AggregateSize(TypeModel type)
    {
        if (!type.ValueType) throw new NotSupportedException($"引用类型不能按值读取: {type.Name}");
        return type.Fields.Max(f => f.Offset + Size(f.Type));
    }
    public static string Integer(int bytes, bool signed) => (bytes, signed) switch
    {
        (1, true) => "System.SByte", (1, false) => "System.Byte",
        (2, true) => "System.Int16", (2, false) => "System.UInt16",
        (4, true) => "System.Int32", (4, false) => "System.UInt32",
        (8, true) => "System.Int64", (8, false) => "System.UInt64",
        _ => throw new NotSupportedException($"整数宽度 {bytes}")
    };
    public string Managed(NativeType type) => type.Kind switch
    {
        "bool" => "System.Boolean", "void" => "System.Void",
        "integer" => Integer(checked((int)type.Bytes), type.Signed),
        "aggregate" => catalog.Types.Single(t => t.NativeName == type.Name ||
            t.NativeName[..^2] + "_Fields" == type.Name).Name,
        "pointer" when catalog.Types.Any(t => !t.ValueType && t.NativeName == type.Pointee) =>
            catalog.Types.Single(t => !t.ValueType && t.NativeName == type.Pointee).Name,
        _ => throw new NotSupportedException($"不能直接转换原生类型 {type.Name}")
    };
    public string ManagedPointee(NativeType type)
    {
        if (type.Kind != "pointer") throw new NotSupportedException("ref 参数必须为原生指针");
        var aggregate = catalog.Types.SingleOrDefault(t => t.NativeName == type.Pointee);
        if (aggregate is not null) return aggregate.Name;
        return type.Pointee switch
        {
            "int32_t" => "System.Int32", "uint32_t" => "System.UInt32", "int64_t" => "System.Int64", "uint64_t" => "System.UInt64",
            "bool" => "System.Boolean", "int8_t" => "System.SByte", "uint8_t" => "System.Byte",
            _ => throw new NotSupportedException($"ref 参数目标类型未支持: {type.Pointee}")
        };
    }
    public Slice[] Span(Storage storage, int width)
    {
        var type = catalog.Type(storage.Root.Type);
        var fields = type.Fields.Where(f => f.Offset < storage.Offset + width &&
            f.Offset + Size(f.Type) > storage.Offset).OrderBy(f => f.Offset).ToArray();
        int offset = storage.Offset;
        foreach (var field in fields)
        {
            if (field.Offset != offset || field.Offset + Size(field.Type) > storage.Offset + width)
                throw new NotSupportedException($"不完整或重叠字段跨度: {type.Name}+{storage.Offset}:{width}");
            offset += Size(field.Type);
        }
        if (offset != storage.Offset + width) throw new NotSupportedException("字段跨度存在空洞");
        return fields.Select(f => new Slice(f, (f.Offset - storage.Offset) * 8)).ToArray();
    }
    public Value Load(Storage storage, string targetType)
    {
        if (storage.Offset == 0 && storage.Root.Type == targetType) return storage.Root;
        var fields = Span(storage, Size(targetType));
        if (fields.Length == 1)
        {
            if (fields[0].Field.Type is "System.Single" or "System.Double")
                throw new NotSupportedException("浮点位重解释尚未实现");
            return Cast(new FieldValue(storage.Root, fields[0].Field), targetType);
        }
        RequirePackable(fields);
        return new PackedLoad(storage.Root, fields, targetType);
    }
    public void RequirePackable(Slice[] fields)
    {
        if (fields.Any(f => f.Field.Type is not ("System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64")))
            throw new NotSupportedException("合并读写目前仅支持完整整数成员");
    }
    public static Value Cast(Value value, string type) => value.Type == type ? value : new Conversion(value, type);
}
