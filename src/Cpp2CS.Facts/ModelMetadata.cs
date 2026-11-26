using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Facts;

/// <summary>v31 类型登记大小含对象头。Packing 是运行时对齐上限，DefaultSize 表示未显式指定大小。</summary>
public readonly record struct LayoutDefinition(int InstanceSize, int? Packing, bool? DefaultSize);
public sealed record LayoutEvidence(IReadOnlyList<LayoutDefinition> Types, IReadOnlyList<int?> FieldOffsets);

/// <summary>Unity 2022 的 LP64 布局与元数据形状。所有偏移计算以字节为单位。</summary>
public sealed class ModelMetadata : IMetadataView
{
    public EntityKeys Keys { get; }
    public MetadataModel Model => Keys.Model;
    private readonly LayoutEvidence? evidence;
    private const int Pointer = 8, Header = 2 * Pointer;
    private readonly Dictionary<string, int> core;
    private readonly HashSet<int> initializers;
    private readonly record struct Storage(int Size, int Alignment, bool References);
    private sealed record Layout(int? Size, int? Actual, int Alignment, bool References, Dictionary<int, int> Offsets);

    public ModelMetadata(EntityKeys keys, LayoutEvidence? evidence = null)
    {
        Keys = keys;
        this.evidence = evidence;
        var coreImage = Model.Images.Single(i => Enumerable.Range(i.FirstType, i.TypeCount)
            .Any(t => Model.Types[t] is { Namespace: "System", Name: "Object", Parent: null, DeclaringType: null }));
        core = Enumerable.Range(coreImage.FirstType, coreImage.TypeCount)
            .Where(t => Model.Types[t] is { Namespace: "System", DeclaringType: null })
            .ToDictionary(t => Model.Types[t].Name, StringComparer.Ordinal);
        initializers = Model.Methods.Where(IsInitializer).Select(m => m.Owner).ToHashSet();
    }

    private static bool IsInitializer(MethodDefinition m) => m.Name == ".cctor" &&
        (m.Flags & (MethodAttributes.Static | MethodAttributes.RTSpecialName)) == (MethodAttributes.Static | MethodAttributes.RTSpecialName);
    private bool IsCore(int index, string name) => core.TryGetValue(name, out int i) && i == index;
    public NamedType CoreType(string name) => core.TryGetValue(name, out int i) ? new(i, []) : throw Missing($"核心库类型 {name}");
    internal static ExpansionException Missing(string what) => new("元数据事实不足", what);
    public EntityRef TypeEntity(TypeReference t) => new(EntityKind.Type, Keys.TypeKey(t) ?? throw Missing($"运行时类型表缺少 {t}"));

    public TypeShape Type(EntityRef entity)
    {
        if (entity.Kind != EntityKind.Type || entity.Key < 0 || entity.Key >= Model.RuntimeTypes.Count) throw Missing($"类型实体 {entity}");
        var t = EntityKeys.Element(Model.RuntimeTypes[(int)entity.Key]);
        if (TypeEntity(t) != entity) throw Missing($"非规范类型实体 {entity}");
        return Shape(t);
    }

    public TypeShape Shape(TypeReference t)
    {
        var entity = TypeEntity(t);
        if (t is ReferenceType) return new(StackKind.ByRef, 64, false, entity);
        if (t is PointerType) return new(StackKind.NativeInt, 64, false, entity);
        if (t is ArrayType) return new(StackKind.Object, 64, false, entity);
        if (t is not NamedType n) throw Missing($"开放类型 {t}");
        if (!Model.Types[n.Definition].ValueType) return new(StackKind.Object, 64, false, entity);
        if (Primitive(n.Definition) is { } p) return new(p.Kind, p.Bits, p.Signed, entity) { TwoValued = IsCore(n.Definition, "Boolean") };
        if (EnumBase(n) is { } underlying) return Shape(underlying) with { Entity = entity, TwoValued = false };
        return new(StackKind.Value, checked(ValueSize(n) * 8), false, entity);
    }

    private (StackKind Kind, int Bits, bool Signed)? Primitive(int index)
    {
        var t = Model.Types[index];
        if (!IsCore(index, t.Name)) return null;
        return t.Name switch
        {
            "Boolean" or "Byte" => (StackKind.Int32, 8, false), "SByte" => (StackKind.Int32, 8, true),
            "Char" or "UInt16" => (StackKind.Int32, 16, false), "Int16" => (StackKind.Int32, 16, true),
            "UInt32" => (StackKind.Int32, 32, false), "Int32" => (StackKind.Int32, 32, true),
            "UInt64" => (StackKind.Int64, 64, false), "Int64" => (StackKind.Int64, 64, true),
            "Single" => (StackKind.Float32, 32, false), "Double" => (StackKind.Float64, 64, false),
            "IntPtr" => (StackKind.NativeInt, 64, true), "UIntPtr" => (StackKind.NativeInt, 64, false),
            _ => null,
        };
    }

    private TypeReference? EnumBase(NamedType t)
    {
        var definition = Model.Types[t.Definition];
        if (definition.Parent is not NamedType p || !IsCore(p.Definition, "Enum")) return null;
        var fields = Fields(t).Where(i => Model.Fields[i].Storage == FieldStorage.Instance).ToArray();
        return fields.Length == 1 ? Model.Fields[fields[0]].Type : throw Missing($"枚举定义 {t.Definition} 的底层字段不唯一");
    }

    public MethodShape Method(EntityRef entity)
    {
        var spec = Keys.DescribeMethod(entity) ?? throw Missing($"方法实体 {entity}");
        var m = Model.Methods[spec.Definition];
        var owner = new NamedType(m.Owner, spec.TypeArguments);
        var d = Model.Types[m.Owner];
        TypeReference Inflate(TypeReference t) => EntityKeys.Inflate(t, owner, spec.Definition, spec.MethodArguments);
        bool instance = !m.Flags.HasFlag(MethodAttributes.Static);
        var self = TypeEntity(owner);
        var parameters = ImmutableArray.CreateBuilder<TypeShape>();
        if (instance) parameters.Add(new(d.ValueType ? StackKind.ByRef : StackKind.Object, 64, false, self));
        foreach (var p in m.Parameters) parameters.Add(Shape(Inflate(p.Type)));
        var dispatch = !instance ? VariantCondition.StaticMethod : d.Flags.HasFlag(TypeAttributes.Interface) ? VariantCondition.InterfaceMethod :
            (m.Flags & (MethodAttributes.Virtual | MethodAttributes.Final)) == MethodAttributes.Virtual &&
            !d.ValueType && !d.Flags.HasFlag(TypeAttributes.Sealed) ? VariantCondition.ClassVirtual : VariantCondition.UniqueTarget;
        var ret = Inflate(m.ReturnType);
        return new(entity, instance, parameters.ToImmutable(), ret is NamedType r && IsCore(r.Definition, "Void") ? null : Shape(ret), dispatch)
        {
            DeclaringType = self, HasInitializer = initializers.Contains(m.Owner), IsTypeInitializer = IsInitializer(m),
            PreciseInitialization = !d.Flags.HasFlag(TypeAttributes.BeforeFieldInit),
        };
    }

    public FieldShape Field(EntityRef entity)
    {
        var (i, owner) = Keys.DescribeField(entity) ?? throw Missing($"字段实体 {entity}");
        var f = Model.Fields[i];
        var d = Model.Types[f.Owner];
        bool instance = f.Storage == FieldStorage.Instance;
        int? offset = FieldOffset(i, owner, instance ? FieldStorage.Instance : FieldStorage.Static);
        int bits = instance && d.ValueType && offset is int at ? checked((at - Header) * 8) : -1;
        return new(entity, TypeEntity(owner), Shape(EntityKeys.Inflate(f.Type, owner)), !instance, initializers.Contains(f.Owner),
            !d.Flags.HasFlag(TypeAttributes.BeforeFieldInit), bits) { Offset = offset };
    }

    private IEnumerable<int> Fields(NamedType t)
    {
        var d = Model.Types[t.Definition];
        return Enumerable.Range(d.FieldCount == 0 ? 0 : d.FirstField, d.FieldCount);
    }

    public int? FieldOffset(int index, NamedType owner, FieldStorage requested)
    {
        var f = Model.Fields[index];
        if (f.Owner != owner.Definition) throw Missing($"字段 {index} 的所属类型不符");
        if (owner.Arguments.Count == 0)
        {
            if (f.Storage != requested || f.Offset is not int at) return null;
            return requested == FieldStorage.Instance && Model.Types[f.Owner].ValueType ? checked(at + Header) : at;
        }
        if (f.Storage == FieldStorage.Instance && requested == FieldStorage.Instance)
            return InstanceLayout(owner, []).Offsets[index];
        if (f.Storage is not (FieldStorage.Static or FieldStorage.ThreadStatic) || requested == FieldStorage.Instance) return null;
        // vm/Field.cpp::IsNormalStatic、IsThreadStatic：普通静态与线程静态各自从零顺序布局。
        int end = 0;
        foreach (int i in Fields(owner))
        {
            var field = Model.Fields[i];
            if (field.Storage is not (FieldStorage.Static or FieldStorage.ThreadStatic)) continue;
            int raw = Evidence.FieldOffsets[i] ?? throw Missing($"泛型静态字段 {i} 缺登记偏移");
            if ((raw < 0 ? FieldStorage.ThreadStatic : FieldStorage.Static) != requested) continue;
            if (Model.Types[owner.Definition].Flags.HasFlag(TypeAttributes.ExplicitLayout))
            {
                if (i == index) return raw & int.MaxValue;
                continue;
            }
            var s = FieldStorageOf(EntityKeys.Inflate(field.Type, owner), []);
            int at = Align(end, s.Alignment);
            if (i == index) return at;
            end = checked(at + Math.Max(s.Size, 1));
        }
        return null;
    }

    private LayoutEvidence Evidence => evidence ?? throw Missing("缺少类型登记大小与布局属性");
    private static int Align(int n, int a) => checked(n + a - 1) & -a;

    /// <summary>vm/Class.cpp::GetValueSize：实例大小减去 Il2CppObject 的大小。</summary>
    public int ValueSize(NamedType type)
    {
        if (!Model.Types[type.Definition].ValueType) throw Missing("类型不是值类型");
        if (type.Arguments.Count == 0 && Model.Types[type.Definition].GenericParameters.Count == 0)
        {
            int size = Evidence.Types[type.Definition].InstanceSize;
            if (size < Header) throw Missing($"定义 {type.Definition} 缺登记大小");
            return size - Header;
        }
        return checked((InstanceLayout(type, []).Size ?? throw Missing($"定义 {type.Definition} 缺实例大小依据")) - Header);
    }

    // metadata/FieldLayout.cpp::GetTypeSizeAndAlignment：引用、按引用与指针占一个指针字；枚举沿用底层类型。
    private Storage FieldStorageOf(TypeReference t, HashSet<string> active)
    {
        if (t is ArrayType) return new(Pointer, Pointer, true);
        if (t is PointerType or ReferenceType) return new(Pointer, Pointer, false);
        if (t is not NamedType n) throw Missing($"字段含开放类型 {t}");
        if (!Model.Types[n.Definition].ValueType) return new(Pointer, Pointer, true);
        if (Primitive(n.Definition) is { } primitive) return new(primitive.Bits / 8, primitive.Bits / 8, false);
        if (EnumBase(n) is { } underlying) return FieldStorageOf(underlying, active);
        var inner = InstanceLayout(n, active);
        return new(checked((inner.Size ?? throw Missing($"字段类型 {n.Definition} 缺大小依据")) - Header), inner.Alignment, inner.References);
    }

    // vm/Class.cpp::SetupFieldsLocked、LayoutFieldsLocked；metadata/FieldLayout.cpp::LayoutFields。
    // Clang 允许复用父类尾部填充。值类型的起始对齐为 1；含托管引用时忽略 packing。
    private Layout InstanceLayout(NamedType owner, HashSet<string> active)
    {
        var d = Model.Types[owner.Definition];
        if (owner.Arguments.Count != d.GenericParameters.Count) throw Missing($"开放泛型定义 {owner.Definition} 无布局");
        string key = EntityKeys.Structure(owner);
        if (!active.Add(key)) throw Missing($"类型 {key} 的值布局递归");
        var parent = d.Parent == null ? null : EntityKeys.Inflate(d.Parent, owner) as NamedType ?? throw Missing("基类不是具名类型");
        var inherited = parent == null ? new Layout(Header, Header, Pointer, false, []) : InstanceLayout(parent, active);
        var fields = Fields(owner).Where(i => Model.Fields[i].Storage == FieldStorage.Instance)
            .Select(i => (Index: i, Storage: FieldStorageOf(EntityKeys.Inflate(Model.Fields[i].Type, owner), active))).ToArray();
        bool references = inherited.References || fields.Any(f => f.Storage.References);
        var registration = evidence?.Types[owner.Definition];
        // vm/GenericClass.cpp::CreateClass 将实例类清零，未从定义复制 packingSize。
        int pack = references || fields.Length == 0 || owner.Arguments.Count != 0 ? 0 : registration?.Packing ?? throw Missing($"定义 {owner.Definition} 缺 packing");
        int alignment = d.ValueType ? 1 : inherited.Alignment;
        int? actual = inherited.Actual;
        var offsets = new Dictionary<int, int>();
        foreach (var (i, storage) in fields)
        {
            int a = pack > 0 ? Math.Min(storage.Alignment, pack) : storage.Alignment;
            int? start = actual;
            int? declared = null;
            if (d.Flags.HasFlag(TypeAttributes.ExplicitLayout))
            {
                // vm/Class.cpp::SetupFieldOffsetsLocked 保留定义给出的显式偏移。
                declared = Evidence.FieldOffsets[i] ?? throw Missing($"显式布局字段 {i} 缺偏移");
                if (declared < 0) throw Missing($"显式布局字段 {i} 的偏移无效");
                // FieldLayout::LayoutInstanceFields 只对非泛型定义用显式起点计算对齐与大小。
                if (owner.Arguments.Count == 0) start = declared.Value;
            }
            int at = Align(start ?? throw Missing($"定义 {owner.Definition} 缺基类数据末端"), a);
            offsets[i] = declared ?? at;
            actual = Math.Max(actual ?? throw Missing($"定义 {owner.Definition} 缺基类数据末端"), checked(at + Math.Max(1, storage.Size)));
            alignment = Math.Max(alignment, a);
        }
        // vm/Class.cpp::UpdateInstanceSizeForGenericClass：显式登记的定义大小是实例大小的下界。
        int? computed = d.FieldCount == 0 ? inherited.Size : fields.Length == 0 && d.ValueType ? Header + 1 :
            actual is int end ? Align(end, alignment) : null;
        int? size = registration?.InstanceSize;
        if (owner.Arguments.Count != 0)
            size = size.HasValue && computed.HasValue ? Math.Max(size.Value, computed.Value) : null;
        if (size < Header) throw Missing($"定义 {owner.Definition} 缺实例大小");
        if (d.FieldCount != 0 && owner.Arguments.Count == 0)
            actual = registration?.DefaultSize switch { true => actual, false => size, null => actual == size ? size : null };
        active.Remove(key);
        return new(size, actual, alignment, references, offsets);
    }
}
