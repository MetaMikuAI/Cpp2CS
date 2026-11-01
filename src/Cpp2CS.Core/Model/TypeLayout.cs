
namespace Cpp2CS.Model;

/// <summary>布局中的一个字段。Offset：实例字段相对对象起始（含 0x10 对象头，值类型同样按装箱布局），静态字段相对 static_fields。</summary>
public sealed record FieldSlot(FieldDef Field, TypeRef Type, int Offset);

/// <summary>
/// 一个（可能是泛型实例的）类型的布局，与 libil2cpp Il2CppClass 中的同名字段一致：
/// InstanceSize 含对象头；值类型的值大小为 InstanceSize - 0x10；MinimumAlignment 用于其作为字段时的对齐。
/// </summary>
public sealed class TypeLayout
{
    public const int ObjectHeaderSize = 0x10;
    public required DefinitionRef Type { get; init; }
    public required int InstanceSize { get; init; }
    public required int ActualSize { get; init; }
    public required int MinimumAlignment { get; init; }
    public required bool HasReferences { get; init; }
    public required IReadOnlyList<FieldSlot> Fields { get; init; }
    public required IReadOnlyList<FieldSlot> Statics { get; init; }
    public required int StaticSize { get; init; }
    public required IReadOnlyList<FieldSlot> ThreadStatics { get; init; }
    /// <summary>非泛型类型：偏移与实例大小取自元数据（运行时同样如此）；Computed 为按算法重算的结果，供核对。</summary>
    public required bool FromMetadata { get; init; }
    public bool IsValueType => Type.Definition.IsValueType;
    public int ValueSize => InstanceSize - TypeLayout.ObjectHeaderSize;
    public FieldSlot? Field(FieldDef field) => Fields.FirstOrDefault(f => f.Field == field) ?? Statics.FirstOrDefault(f => f.Field == field);
}

/// <summary>类型服务消费布局事实，不依赖布局推断的实现。</summary>
public interface ITypeLayouts
{
    TypeLayout? Of(DefinitionRef type);
    (int Size, int Alignment) SizeAndAlignment(TypeRef type);
    (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type);
}
