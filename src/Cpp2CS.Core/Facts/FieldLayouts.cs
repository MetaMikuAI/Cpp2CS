using System.Reflection;
using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>布局中的一个字段。Offset：实例字段相对对象起始（含 0x10 对象头，值类型同样按装箱布局），静态字段相对 static_fields。</summary>
public sealed record FieldSlot(FieldDef Field, TypeRef Type, int Offset);

/// <summary>
/// 一个（可能是泛型实例的）类型的布局，与 libil2cpp Il2CppClass 中的同名字段一致：
/// InstanceSize 含对象头；值类型的值大小为 InstanceSize - 0x10；MinimumAlignment 用于其作为字段时的对齐。
/// </summary>
public sealed class TypeLayout
{
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
    public int ValueSize => InstanceSize - RuntimeLayout.ObjectHeaderSize;
    public FieldSlot? Field(FieldDef field) => Fields.FirstOrDefault(f => f.Field == field) ?? Statics.FirstOrDefault(f => f.Field == field);
}

/// <summary>
/// 按 libil2cpp 2022.3（vm/Class.cpp LayoutFieldsLocked、metadata/FieldLayout.cpp LayoutFields）计算字段布局。
/// 非泛型类型运行时直接使用元数据中的偏移与实例大小，这里同样采用元数据值，并保留算法重算结果用于全量核对；
/// 泛型实例运行时才计算布局，这里按同一算法以代入实参后的字段类型计算。
/// 要点：从父类的 actualSize（而非对齐后的 instance_size）开始排布（clang 复用尾部填充）；
/// 含引用的类型忽略 packing；非泛型的显式布局取元数据偏移；无实例字段的值类型大小为 1。
/// </summary>
public sealed class FieldLayouts
{
    private const int EmptyStructSize = 1;
    private readonly ProgramModel model;
    private readonly object gate = new();
    private readonly Dictionary<(DefinitionRef Type, string Binding), TypeLayout> cache = new();
    private readonly Dictionary<(DefinitionRef Type, string Binding), TypeLayout> computed = new();
    private readonly HashSet<(DefinitionRef Type, string Binding)> active = new();
    /// <summary>实例部分已排好、静态部分尚在计算的布局：类型以自身值类型作静态字段时（如 Vector2.zeroVector）由此取大小。</summary>
    private readonly Dictionary<((DefinitionRef Type, string Binding), bool), TypeLayout> provisional = new();

    public FieldLayouts(ProgramModel model) => this.model = model;

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
        var key = (type, NativeBindings.Key(type));
        var store = preferMetadata ? cache : computed;
        if (store.TryGetValue(key, out var known)) return known;
        if (provisional.TryGetValue((key, preferMetadata), out var partial)) return partial;
        var definition = type.Definition;
        if (definition.GenericParameters.Count != type.Arguments.Count) return null;
        if (!active.Add(key)) throw new InvalidDataException($"布局递归：{type}");
        try
        {
            var layout = Build(type, preferMetadata);
            store[key] = layout;
            return layout;
        }
        finally { active.Remove(key); }
    }

    private TypeLayout Build(DefinitionRef type, bool preferMetadata)
    {
        var definition = type.Definition;
        var arguments = type.Arguments;
        var generic = arguments.Count > 0;
        var valueType = definition.IsValueType;

        TypeLayout? parent = definition.BaseType?.Substitute(arguments, []) is DefinitionRef baseType ? Layout(baseType, preferMetadata) : null;
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
            actualSize = instanceSize = RuntimeLayout.ObjectHeaderSize;
            minimumAlignment = 8;
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
            var explicitLayout = (definition.Attributes & TypeAttributes.ExplicitLayout) != 0 && !generic;
            var (classSize, actualClassSize, alignment, offsets) = LayoutFields(instance, FieldType, instanceSize, actualSize, minimumAlignment, packing,
                explicitLayout ? f => MetadataOffset(f) : null, preferMetadata);
            for (var i = 0; i < instance.Length; i++) fields.Add(new FieldSlot(instance[i], FieldType(instance[i]), offsets[i]));
            instanceSize = classSize;
            if (valueType && instance.Length == 0)
                instanceSize = actualClassSize = EmptyStructSize + RuntimeLayout.ObjectHeaderSize;
            instanceSize = UpdateForGeneric(definition, generic, instanceSize);
            instanceSize = ExplicitClassSize(definition, generic, instanceSize, actualClassSize);
            minimumAlignment = alignment;
            actualSize = generic || definition.ClassSizeIsDefault != false ? actualClassSize : instanceSize;
            provisional[((type, NativeBindings.Key(type)), preferMetadata)] = new TypeLayout
            {
                Type = type, InstanceSize = instanceSize, ActualSize = actualSize, MinimumAlignment = minimumAlignment, HasReferences = hasReferences,
                Fields = fields, Statics = [], StaticSize = 0, ThreadStatics = [], FromMetadata = false,
            };

            var (statSize, _, _, statOffsets) = LayoutFields(statics, FieldType, 0, 0, 1, 0, null, preferMetadata);
            staticSize = statSize;
            for (var i = 0; i < statics.Length; i++) staticSlots.Add(new FieldSlot(statics[i], FieldType(statics[i]), statOffsets[i]));
            var (_, _, _, threadOffsets) = LayoutFields(threadStatics, FieldType, 0, 0, 1, 0, null, preferMetadata);
            for (var i = 0; i < threadStatics.Length; i++) threadSlots.Add(new FieldSlot(threadStatics[i], FieldType(threadStatics[i]), threadOffsets[i]));
        }
        else
        {
            // 没有任何字段：值类型按 1 字节空结构（il2cpp.exe 同样如此，泛型实例经 UpdateInstanceSizeForGenericClass 取定义的 17）
            if (valueType) instanceSize = actualSize = EmptyStructSize + RuntimeLayout.ObjectHeaderSize;
            instanceSize = ExplicitClassSize(definition, generic, UpdateForGeneric(definition, generic, instanceSize), actualSize);
        }
        provisional.Remove(((type, NativeBindings.Key(type)), preferMetadata));

        var fromMetadata = false;
        if (preferMetadata && !generic && definition.Size > 0)
        {
            // 运行时：非泛型类型的偏移与实例大小来自元数据（Il2CppTypeDefinitionSizes 与 fieldOffsets）
            fromMetadata = true;
            instanceSize = valueType ? definition.Size + RuntimeLayout.ObjectHeaderSize : definition.Size;
            fields = fields.Select(f => MetadataOffset(f.Field) is { } m ? f with { Offset = m } : f).ToList();
            staticSlots = staticSlots.Select(f => f.Field.Offset >= 0 ? f with { Offset = f.Field.Offset } : f).ToList();
        }
        return new TypeLayout
        {
            Type = type,
            InstanceSize = instanceSize,
            ActualSize = actualSize,
            MinimumAlignment = minimumAlignment,
            HasReferences = hasReferences,
            Fields = fields,
            Statics = staticSlots,
            StaticSize = staticSize,
            ThreadStatics = threadSlots,
            FromMetadata = fromMetadata,
        };
    }

    /// <summary>元数据中的实例字段偏移，换算为含对象头的对象相对偏移；未知返回 null。</summary>
    private static int? MetadataOffset(FieldDef field)
    {
        if (field.Offset < 0) return null;
        return field.Owner.IsValueType && !field.IsStatic ? field.Offset + RuntimeLayout.ObjectHeaderSize : field.Offset;
    }

    /// <summary>
    /// 非泛型类型声明了 StructLayout(Size = N)（元数据 ClassSize：固定缓冲区、__StaticArrayInitTypeSize=N、InputSystem 命令结构等）时，
    /// 实例大小为 max(声明值, 未对齐的字段末端)，不再按最小对齐取整；这与元数据 Il2CppTypeDefinitionSizes 一致。
    /// </summary>
    private static int ExplicitClassSize(TypeDef definition, bool generic, int instanceSize, int actualSize)
    {
        if (generic || definition.ClassSizeIsDefault != false || definition.Size <= 0) return instanceSize;
        var declared = definition.IsValueType ? definition.Size + RuntimeLayout.ObjectHeaderSize : definition.Size;
        return Math.Max(declared, actualSize);
    }

    /// <summary>
    /// 实例大小由运行时 C++ 结构决定、不由字段推出的类型：Il2CppArray、Il2CppComObject，
    /// 以及完全共享泛型（2022.1+）的占位类型 __Il2CppFullySharedGenericType / __Il2CppFullySharedGenericStructType。
    /// </summary>
    private static readonly HashSet<string> RuntimeDefinedTypes = ["System.Array", "System.__Il2CppComObject", "System.__Il2CppComDelegate",
        "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType", "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericStructType"];

    /// <summary>
    /// 实参含完全共享占位类型的泛型实例：共享代码里的字段偏移、值大小由运行时经 RGCTX 读取，不是代码中的常量，
    /// 这类实例的布局只描述占位类型本身，不能用来解释共享代码的访存偏移。
    /// </summary>
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
    /// 显式布局值类型的对齐：il2cpp.exe（生成元数据）与运行时 LayoutFields（对显式偏移再对齐、取字段最大对齐）结论不同，
    /// 例如 InputActionState.TriggerState（Explicit, Size=68，含 double）在元数据中按 4 字节对齐嵌入，运行时算法为 8。
    /// 非泛型容器运行时读元数据，不受影响；泛型实例以运行时算法为准。
    /// </summary>
    private bool InvolvesExplicitStruct(TypeDef definition) => definition.Fields.Any(f => !f.IsStatic
        && Underlying(f.Type) is DefinitionRef { Definition: { IsValueType: true } t } && (t.Attributes & TypeAttributes.ExplicitLayout) != 0);

    /// <summary>泛型实例：若泛型定义在元数据中有显式（更大的）实例大小，以其为准。</summary>
    private static int UpdateForGeneric(TypeDef definition, bool generic, int instanceSize)
    {
        if (!generic || definition.Size <= 0) return instanceSize;
        var declared = definition.IsValueType ? definition.Size + RuntimeLayout.ObjectHeaderSize : definition.Size;
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
            case GenericParameterRef { NativeScalar: { } scalar }: return TrySizeAndAlignment(scalar, preferMetadata);
            case GenericParameterRef { NativeAggregate: { } aggregate }: return TrySizeAndAlignment(aggregate, preferMetadata);
            case ByRefRef or PointerRef or ArrayRef or GenericParameterRef or PrimitiveRef:
                return (8, 8);
            case DefinitionRef d:
                if (PrimitiveSize(d) is { } primitive) return (primitive, primitive);
                if (!d.Definition.IsValueType) return (8, 8);
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
    private static bool IsReference(TypeRef type) => type switch
    {
        ArrayRef => true,
        DefinitionRef d => !d.Definition.IsValueType && PrimitiveSize(d) is null || d.Definition.FullName is "System.String" or "System.Object",
        _ => false,
    };

    private static bool IsPrimitive(DefinitionRef d) => PrimitiveSize(d) is not null;

    private static int? PrimitiveSize(DefinitionRef d)
    {
        var t = d.Definition;
        if (t.Assembly != "mscorlib.dll" || t.Namespace != "System" || t.DeclaringType is not null) return null;
        return t.Name switch
        {
            "Boolean" or "SByte" or "Byte" => 1,
            "Int16" or "UInt16" or "Char" => 2,
            "Int32" or "UInt32" or "Single" => 4,
            "Int64" or "UInt64" or "Double" or "IntPtr" or "UIntPtr" => 8,
            _ => null,
        };
    }

    /// <summary>对全部非泛型类型，以算法重算并与元数据（运行时实际使用的值）逐字段核对。</summary>
    public void Check(FactChecks checks)
    {
        var instanceMismatch = new List<string>();
        var sizeMismatch = new List<string>();
        var explicitDivergence = new List<string>();
        var runtimeDefined = 0;
        var staticMismatch = new List<string>();
        int types = 0, fieldCount = 0, staticCount = 0;
        var failed = new List<string>();
        foreach (var definition in model.Types)
        {
            if (definition.GenericParameters.Count > 0 || definition.IsInterface || definition.Size <= 0 || definition.Name == "<Module>") continue;
            var type = new DefinitionRef(definition, []);
            var layout = Compute(type);
            if (layout is null) { failed.Add($"{definition}: 没有可用布局"); continue; }
            types++;
            if (RuntimeDefinedTypes.Contains(definition.FullName)) { runtimeDefined++; continue; }
            var known = InvolvesExplicitStruct(definition);
            var declared = definition.IsValueType ? definition.Size + RuntimeLayout.ObjectHeaderSize : definition.Size;
            if (layout.InstanceSize != declared) (known ? explicitDivergence : sizeMismatch).Add($"{definition}: 算法 0x{layout.InstanceSize:x}，元数据 0x{declared:x}");
            foreach (var slot in layout.Fields)
            {
                if (MetadataOffset(slot.Field) is not { } m) continue;
                fieldCount++;
                if (m != slot.Offset) (known ? explicitDivergence : instanceMismatch).Add($"{slot.Field}（{slot.Type}）：算法 0x{slot.Offset:x}，元数据 0x{m:x}");
            }
            foreach (var slot in layout.Statics)
            {
                if (slot.Field.Offset < 0) continue;
                staticCount++;
                if (slot.Field.Offset != slot.Offset) staticMismatch.Add($"{slot.Field}：算法 0x{slot.Offset:x}，元数据 0x{slot.Field.Offset:x}");
            }
        }
        checks.Add("layout.compute", "Error", types + failed.Count, failed, "非泛型类型均能按算法完成布局");
        checks.Add("layout.instance-size", "Error", types, sizeMismatch,
            $"算法重算的 instance_size 与元数据 Il2CppTypeDefinitionSizes 一致（运行时定义大小的类型 {runtimeDefined} 个不比较）");
        checks.Add("layout.explicit-struct-alignment", "Warning", types, explicitDivergence,
            "含显式布局值类型字段的非泛型类型：元数据（il2cpp.exe）与运行时算法对其对齐的结论不同；运行时对非泛型类型读元数据，泛型实例以算法为准");
        checks.Add("layout.instance-fields", "Error", fieldCount, instanceMismatch, "算法重算的实例字段偏移与元数据 fieldOffsets 一致");
        checks.Add("layout.static-fields", "Error", staticCount, staticMismatch, "算法重算的静态字段偏移与元数据一致");

        // 泛型实例：元数据注册的全部运行时类型中出现的泛型实例
        var instances = model.RuntimeTypes.OfType<DefinitionRef>().Where(d => d.Arguments.Count > 0 && !ContainsGenericParameter(d)).Distinct().ToArray();
        var genericFailures = new List<string>();
        var valueTypes = 0;
        foreach (var instance in instances)
        {
            var layout = Of(instance);
            if (layout is null) genericFailures.Add($"{instance}: 没有可用布局");
            else if (layout.IsValueType) valueTypes++;
        }
        checks.Add("layout.generic-instances", "Error", instances.Length, genericFailures,
            $"元数据中全部封闭泛型实例类型均能计算布局（其中值类型 {valueTypes} 个；实参含完全共享占位类型、偏移需经 RGCTX 的 {instances.Count(IsFullyShared)} 个）");
    }

    private static bool ContainsGenericParameter(TypeRef type) => type switch
    {
        GenericParameterRef => true,
        DefinitionRef d => d.Arguments.Any(ContainsGenericParameter),
        ArrayRef a => ContainsGenericParameter(a.Element),
        PointerRef p => ContainsGenericParameter(p.Element),
        ByRefRef r => ContainsGenericParameter(r.Element),
        _ => false,
    };
}
