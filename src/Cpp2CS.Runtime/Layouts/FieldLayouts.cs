using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Runtime.Layouts;

/// <summary>
/// 按 libil2cpp 2022.3（vm/Class.cpp LayoutFieldsLocked、metadata/FieldLayout.cpp LayoutFields）计算字段布局。
/// 非泛型类型运行时直接使用元数据中的偏移与实例大小，这里同样采用元数据值，并保留算法重算结果用于全量核对；
/// 泛型实例运行时才计算布局，这里按同一算法以代入实参后的字段类型计算。
/// 要点：从父类的 actualSize（而非对齐后的 instance_size）开始排布（clang 复用尾部填充）；
/// 含引用的类型忽略 packing；非泛型的显式布局取元数据偏移；无实例字段的值类型大小为 1。
/// </summary>
public sealed class FieldLayouts : ITypeLayouts
{
    private const int EmptyStructSize = 1;
    private readonly RuntimeSpec spec;
    private readonly int headerSize;
    private readonly int pointerSize;
    private readonly int pointerAlignment;
    private readonly object gate = new();
    private readonly Dictionary<DefinitionRef, TypeLayout> cache = new();
    private readonly Dictionary<DefinitionRef, TypeLayout> computed = new();
    private readonly HashSet<DefinitionRef> active = new();
    /// <summary>实例部分已排好、静态部分尚在计算的布局：类型以自身值类型作静态字段时由此取大小。</summary>
    private readonly Dictionary<(DefinitionRef, bool), TypeLayout> provisional = new();

    public FieldLayouts(RuntimeSpec spec, int pointerSize, int pointerAlignment)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(pointerSize);
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(pointerAlignment);
        if ((pointerAlignment & (pointerAlignment - 1)) != 0) throw new ArgumentException("指针对齐必须是二的幂", nameof(pointerAlignment));
        if (spec.Layout.Primitive("void *") is var pointer && (pointer.Size != pointerSize || pointer.Alignment != pointerAlignment))
            throw new ArgumentException("数据模型与运行时规格的指针布局不一致");
        this.spec = spec;
        headerSize = checked((int)spec.Layout.ObjectHeaderSize);
        this.pointerSize = pointerSize;
        this.pointerAlignment = pointerAlignment;
    }

    /// <summary>类型的布局；泛型定义（未代入实参）没有运行时布局，返回 null。</summary>
    public TypeLayout? Of(DefinitionRef type) => Layout(type, preferMetadata: true);

    /// <summary>按算法重算（不采用元数据值），用于核对。</summary>
    public TypeLayout? Compute(DefinitionRef type) => Layout(type, preferMetadata: false);

    private TypeLayout? Layout(DefinitionRef type, bool preferMetadata)
    {
        // 递归构建中的临时布局只对持锁线程可见，完成后共享缓存。
        lock (gate) return LayoutCore(type, preferMetadata);
    }

    private TypeLayout? LayoutCore(DefinitionRef type, bool preferMetadata)
    {
        var key = type;
        var store = preferMetadata ? cache : computed;
        if (store.TryGetValue(key, out var known)) return known;
        if (provisional.TryGetValue((key, preferMetadata), out var partial)) return partial;
        var definition = type.Definition;
        if (definition.GenericParameters.Count != type.Arguments.Count || type.ContainsGenericParameter()) return null;
        if (definition.PackingSize < 0 || definition.ClassSizeIsDefault is null) return null;
        if (definition.ClassSizeIsDefault == false && definition.Size <= 0) return null;
        if ((definition.PackingSize & (definition.PackingSize - 1)) != 0) throw new InvalidDataException($"无效打包值：{type}");
        if (preferMetadata && type.Arguments.Count == 0 && (definition.Size <= 0 || definition.Fields.Any(f => !f.IsThreadStatic && (f.Attributes & FieldAttributes.Literal) == 0 && f.Offset < 0))) return null;
        if (!active.Add(key)) throw new InvalidDataException($"布局递归：{type}");
        try
        {
            var layout = Build(type, preferMetadata);
            store[key] = layout;
            return layout;
        }
        finally { active.Remove(key); provisional.Remove((key, preferMetadata)); }
    }

    private TypeLayout Build(DefinitionRef type, bool preferMetadata)
    {
        var definition = type.Definition;
        var arguments = type.Arguments;
        var generic = arguments.Count > 0;
        var valueType = definition.IsValueType;

        TypeLayout? parent = null;
        if (definition.BaseType is { } declaredBase)
        {
            if (declaredBase.Substitute(arguments, []) is not DefinitionRef baseType || Layout(baseType, preferMetadata) is not { } baseLayout)
                throw new InvalidDataException($"类型 {type} 的父类没有可用布局");
            parent = baseLayout;
        }
        int instanceSize, actualSize, minimumAlignment;
        var hasReferences = parent?.HasReferences ?? false;
        if (parent is not null)
        {
            instanceSize = parent.InstanceSize;
            actualSize = parent.ActualSize;
            minimumAlignment = valueType ? 1 : parent.MinimumAlignment;
        }
        else
        {
            actualSize = instanceSize = headerSize;
            minimumAlignment = valueType ? 1 : pointerAlignment;
        }

        var instance = definition.Fields.Where(f => !f.IsStatic).ToArray();
        var statics = definition.Fields.Where(f => f.IsStatic && !f.IsThreadStatic && (f.Attributes & FieldAttributes.Literal) == 0).ToArray();
        var threadStatics = definition.Fields.Where(f => f.IsStatic && f.IsThreadStatic).ToArray();
        TypeRef FieldType(FieldDef f) => f.Type.Substitute(arguments, []);

        var fields = new List<FieldSlot>();
        var staticSlots = new List<FieldSlot>();
        var threadSlots = new List<FieldSlot>();
        var staticSize = 0;
        if (definition.Fields.Count > 0)
        {
            foreach (var field in instance)
            {
                var t = Underlying(FieldType(field));
                if (IsReference(t) || (t is DefinitionRef { Definition.IsValueType: true } s && !IsPrimitive(s) && Layout(s, preferMetadata)?.HasReferences == true))
                    hasReferences = true;
            }
            var packing = hasReferences ? 0 : Math.Max(0, definition.PackingSize);
            var explicitLayout = (definition.Attributes & TypeAttributes.LayoutMask) == TypeAttributes.ExplicitLayout;
            if (explicitLayout && generic) throw new InvalidDataException($"泛型显式布局不受运行时支持：{type}");
            if (explicitLayout && instance.Any(f => MetadataOffset(f) is null)) throw new InvalidDataException($"显式布局缺字段偏移：{type}");
            var (classSize, actualClassSize, alignment, offsets) = LayoutFields(instance, FieldType, instanceSize, actualSize, minimumAlignment, packing,
                explicitLayout ? f => MetadataOffset(f) : null, preferMetadata);
            for (var i = 0; i < instance.Length; i++) fields.Add(new FieldSlot(instance[i], FieldType(instance[i]), offsets[i]));
            instanceSize = classSize;
            if (valueType && instance.Length == 0)
                instanceSize = actualClassSize = EmptyStructSize + headerSize;
            instanceSize = UpdateForGeneric(definition, generic, instanceSize);
            instanceSize = ExplicitClassSize(definition, generic, instanceSize, actualClassSize);
            minimumAlignment = alignment;
            actualSize = generic || definition.ClassSizeIsDefault != false ? actualClassSize : instanceSize;
            provisional[(type, preferMetadata)] = new TypeLayout
            {
                ObjectHeaderSize = headerSize,
                Type = type,
                InstanceSize = instanceSize,
                ActualSize = actualSize,
                MinimumAlignment = minimumAlignment,
                HasReferences = hasReferences,
                Fields = fields.AsReadOnly(),
                Statics = [],
                StaticSize = 0,
                ThreadStatics = [],
                FromMetadata = false,
            };

            var (statSize, _, _, statOffsets) = LayoutFields(statics, FieldType, 0, 0, 1, 0, null, preferMetadata);
            staticSize = statSize;
            for (var i = 0; i < statics.Length; i++) staticSlots.Add(new FieldSlot(statics[i], FieldType(statics[i]), statOffsets[i]));
            var (_, _, _, threadOffsets) = LayoutFields(threadStatics, FieldType, 0, 0, 1, 0, null, preferMetadata);
            for (var i = 0; i < threadStatics.Length; i++) threadSlots.Add(new FieldSlot(threadStatics[i], FieldType(threadStatics[i]), threadOffsets[i]));
        }
        else
        {
            // 没有任何字段：值类型按 1 字节空结构（il2cpp.exe 同样如此，泛型实例经 UpdateInstanceSizeForGenericClass 取定义的声明大小）
            if (valueType) instanceSize = actualSize = EmptyStructSize + headerSize;
            instanceSize = ExplicitClassSize(definition, generic, UpdateForGeneric(definition, generic, instanceSize), actualSize);
        }
        provisional.Remove((type, preferMetadata));

        var fromMetadata = false;
        if (preferMetadata && !generic && definition.Size > 0)
        {
            // 运行时：非泛型类型的偏移与实例大小来自元数据（Il2CppTypeDefinitionSizes 与 fieldOffsets）
            fromMetadata = true;
            instanceSize = valueType ? definition.Size + headerSize : definition.Size;
            fields = fields.Select(f => MetadataOffset(f.Field) is { } m ? f with { Offset = m } : f).ToList();
            staticSlots = staticSlots.Select(f => f.Field.Offset >= 0 ? f with { Offset = f.Field.Offset } : f).ToList();
        }
        return new TypeLayout
        {
            ObjectHeaderSize = headerSize,
            Type = type,
            InstanceSize = instanceSize,
            ActualSize = actualSize,
            MinimumAlignment = minimumAlignment,
            HasReferences = hasReferences,
            Fields = fields.AsReadOnly(),
            Statics = staticSlots.AsReadOnly(),
            StaticSize = staticSize,
            ThreadStatics = threadSlots.AsReadOnly(),
            FromMetadata = fromMetadata,
        };
    }

    /// <summary>元数据中的实例字段偏移，换算为含对象头的对象相对偏移；未知返回 null。</summary>
    private int? MetadataOffset(FieldDef field)
    {
        if (field.Offset < 0) return null;
        return field.Owner.IsValueType && !field.IsStatic ? field.Offset + headerSize : field.Offset;
    }

    /// <summary>
    /// 非泛型类型声明了 StructLayout(Size = N)（元数据 ClassSize，例如固定缓冲区）时，
    /// 实例大小为 max(声明值, 未对齐的字段末端)，不再按最小对齐取整；这与元数据 Il2CppTypeDefinitionSizes 一致。
    /// </summary>
    private int ExplicitClassSize(TypeDef definition, bool generic, int instanceSize, int actualSize)
    {
        if (generic || definition.ClassSizeIsDefault != false || definition.Size <= 0) return instanceSize;
        var declared = definition.IsValueType ? definition.Size + headerSize : definition.Size;
        return Math.Max(declared, actualSize);
    }

    /// <summary>泛型实例：若泛型定义在元数据中有显式（更大的）实例大小，以其为准。</summary>
    private int UpdateForGeneric(TypeDef definition, bool generic, int instanceSize)
    {
        if (!generic || definition.Size <= 0) return instanceSize;
        var declared = definition.IsValueType ? definition.Size + headerSize : definition.Size;
        return Math.Max(declared, instanceSize);
    }

    private (int ClassSize, int ActualClassSize, int MinimumAlignment, int[] Offsets) LayoutFields(FieldDef[] fields, Func<FieldDef, TypeRef> typeOf,
        int parentSize, int actualParentSize, int parentAlignment, int packing, Func<FieldDef, int?>? explicitOffset, bool preferMetadata)
    {
        var actual = actualParentSize;
        var minimumAlignment = parentAlignment;
        var offsets = new int[fields.Length];
        for (var i = 0; i < fields.Length; i++)
        {
            var (size, alignment) = SizeAndAlignment(typeOf(fields[i]), preferMetadata);
            if (packing > 0) alignment = Math.Min(alignment, packing);
            // 显式布局取元数据偏移原值：il2cpp.exe 不再对齐；运行时的再对齐只用于调试断言，且显式布局只出现在非泛型类型
            var offset = explicitOffset?.Invoke(fields[i]) is { } fixedOffset ? fixedOffset : (actual + alignment - 1) & ~(alignment - 1);
            offsets[i] = offset;
            actual = Math.Max(actual, offset + Math.Max(size, 1));
            minimumAlignment = Math.Max(minimumAlignment, alignment);
        }
        var classSize = (actual & (minimumAlignment - 1)) != 0 ? (actual + minimumAlignment - 1) & ~(minimumAlignment - 1) : actual;
        _ = parentSize;
        return (classSize, actual, minimumAlignment, offsets);
    }

    /// <summary>作为字段时的大小与对齐（FieldLayout::GetTypeSizeAndAlignment）。</summary>
    public (int Size, int Alignment) SizeAndAlignment(TypeRef type) => SizeAndAlignment(type, preferMetadata: true);

    /// <summary>未绑定或不支持的字段类型没有布局；递归和损坏的元数据仍直接报错。</summary>
    public (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type) => TrySizeAndAlignment(type, preferMetadata: true);

    private (int Size, int Alignment) SizeAndAlignment(TypeRef type, bool preferMetadata) =>
        TrySizeAndAlignment(type, preferMetadata) ?? throw new InvalidDataException($"类型 {type} 没有可用字段布局");

    private (int Size, int Alignment)? TrySizeAndAlignment(TypeRef type, bool preferMetadata)
    {
        switch (type)
        {
            case GenericParameterRef: return null;
            case ByRefRef or PointerRef or ArrayRef:
            case PrimitiveRef { Name: "nint" }:
                return (pointerSize, pointerAlignment);
            case DefinitionRef d:
                if (PrimitiveSize(d) is { } primitive)
                {
                    if (ManagedTypes.PrimitiveName(d) is "IntPtr" or "UIntPtr") return (pointerSize, pointerAlignment);
                    var name = ManagedTypes.PrimitiveName(d) switch
                    {
                        "Boolean" or "Byte" or "SByte" => "char",
                        "Char" or "Int16" or "UInt16" => "short",
                        "Int32" or "UInt32" => "int",
                        "Int64" or "UInt64" => "long long",
                        "Single" => "float", "Double" => "double",
                        _ => throw new InvalidDataException("未知基元")
                    };
                    return (primitive, checked((int)spec.Layout.Primitive(name).Alignment));
                }
                if (!d.Definition.IsValueType) return (pointerSize, pointerAlignment);
                if (d.Definition.IsEnum) return TrySizeAndAlignment(EnumUnderlying(d), preferMetadata);
                return Layout(d, preferMetadata) is { } layout ? (layout.ValueSize, layout.MinimumAlignment) : null;
            default:
                return null;
        }
    }

    private static TypeRef EnumUnderlying(DefinitionRef type) =>
        type.Definition.Fields.FirstOrDefault(f => !f.IsStatic)?.Type ?? throw new InvalidDataException($"枚举 {type} 没有 value__ 字段");

    private static TypeRef Underlying(TypeRef type) => type is DefinitionRef { Definition.IsEnum: true } e ? EnumUnderlying(e) : type;

    /// <summary>Type::IsReference：string、数组、类、object、引用类型泛型实例。</summary>
    private bool IsReference(TypeRef type) => type switch
    {
        ArrayRef => true,
        DefinitionRef d => !d.Definition.IsValueType && PrimitiveSize(d) is null || d.Definition.FullName is "System.String" or "System.Object",
        _ => false,
    };

    private bool IsPrimitive(DefinitionRef d) => PrimitiveSize(d) is not null;

    private int? PrimitiveSize(DefinitionRef d)
    {
        var t = d.Definition;
        if (t.Assembly != "mscorlib.dll" || t.Namespace != "System" || t.DeclaringType is not null) return null;
        return t.Name switch
        {
            "Boolean" or "SByte" or "Byte" => 1,
            "Int16" or "UInt16" or "Char" => 2,
            "Int32" or "UInt32" or "Single" => 4,
            "Int64" or "UInt64" or "Double" => 8,
            "IntPtr" or "UIntPtr" => pointerSize,
            _ => null,
        };
    }

}
