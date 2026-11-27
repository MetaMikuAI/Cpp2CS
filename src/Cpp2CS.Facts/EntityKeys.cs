using Cpp2CS.Model;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Facts;

/// <summary>实体编号取自模型行序与模型中可推导的类型结构。</summary>
public sealed class EntityKeys
{
    public const long InstanceBase = 1L << 32;
    public MetadataModel Model { get; }
    private readonly ModelTypeIndex types;
    private readonly Dictionary<string, int> instances = new(StringComparer.Ordinal);
    private readonly Dictionary<string, int> literals = new(StringComparer.Ordinal);

    public EntityKeys(MetadataModel model)
    {
        Model = model;
        types = new(model);
        for (int i = 0; i < model.MethodInstances.Count; i++) instances.TryAdd(Structure(model.MethodInstances[i]), i);
        for (int i = 0; i < model.StringLiterals.Count; i++) literals.TryAdd(model.StringLiterals[i], i);
    }

    private static string Arguments(IReadOnlyList<TypeReference> types) => "(" + string.Join(",", types.Select(Structure)) + ")";
    private static string Structure(MethodInstance method) =>
        FormattableString.Invariant($"{method.Definition}{Arguments(method.TypeArguments)}{Arguments(method.MethodArguments)}");

    internal static string Structure(TypeReference type) => type switch
    {
        NamedType n => FormattableString.Invariant($"D{n.Definition}{Arguments(n.Arguments)}"),
        ReferenceType r => Structure(r.Element),
        PointerType p => "*" + Structure(p.Element),
        ArrayType a => a.Vector ? "V" + Structure(a.Element) : FormattableString.Invariant($"A{a.Rank}:{Structure(a.Element)}"),
        VariableType v => FormattableString.Invariant($"{(v.Method ? "M" : "T")}{v.Owner}:{v.Position}"),
        _ => throw new ArgumentOutOfRangeException(nameof(type)),
    };

    public long? TypeKey(TypeReference type) => types.Key(type);
    public TypeReference? DescribeType(EntityRef entity) => entity.Kind == EntityKind.Type ? types.Describe(entity.Key) : null;
    public long? MethodKey(int definition) => (uint)definition < Model.Methods.Count ? definition : null;
    public long? MethodKey(MethodInstance method) => instances.TryGetValue(Structure(method), out int key) ? InstanceBase + key : null;
    public long? StringKey(string value) => literals.TryGetValue(value, out int key) ? key : null;
    public long? FieldKey(int definition, NamedType owner)
    {
        if ((uint)definition >= Model.Fields.Count || Model.Fields[definition].Owner != owner.Definition) return null;
        if (owner.Arguments.Count == 0) return definition;
        return TypeKey(owner) is long key ? ((key + 1) << 32) | (uint)definition : null;
    }

    public MethodInstance? DescribeMethod(EntityRef entity)
    {
        if (entity.Kind != EntityKind.Method || entity.Key < 0) return null;
        if (entity.Key < Model.Methods.Count) return new((int)entity.Key, [], []);
        long index = entity.Key - InstanceBase;
        if (index < 0 || index >= Model.MethodInstances.Count) return null;
        var instance = Model.MethodInstances[(int)index];
        return MethodKey(instance) == entity.Key ? instance : null;
    }

    public (int Index, NamedType Owner)? DescribeField(EntityRef entity)
    {
        uint field = unchecked((uint)entity.Key);
        if (entity.Kind != EntityKind.Field || entity.Key < 0 || field >= Model.Fields.Count) return null;
        int declaration = Model.Fields[(int)field].Owner;
        long high = entity.Key >> 32;
        if (high == 0) return ((int)field, new(declaration, []));
        if (types.Describe(high - 1) is not NamedType owner || owner.Arguments.Count == 0 || owner.Definition != declaration) return null;
        return ((int)field, owner);
    }

    internal static TypeReference Element(TypeReference type) => type is ReferenceType reference ? reference.Element : type;

    /// <summary>metadata/GenericMetadata.cpp::InflateIfNeeded：依所属的类型与方法容器按位置代入。</summary>
    public static TypeReference Inflate(TypeReference type, NamedType owner, int method = -1, IReadOnlyList<TypeReference>? arguments = null) =>
        Substitute(type, v => v switch
        {
            { Method: false } when v.Owner == owner.Definition && (uint)v.Position < owner.Arguments.Count => owner.Arguments[v.Position],
            { Method: true } when v.Owner == method && arguments != null && (uint)v.Position < arguments.Count => arguments[v.Position],
            _ => v,
        });

    internal static TypeReference Substitute(TypeReference type, Func<VariableType, TypeReference> variable) => type switch
    {
        VariableType v => variable(v),
        NamedType n when n.Arguments.Count != 0 => n with { Arguments = n.Arguments.Select(a => Substitute(a, variable)).ToArray() },
        ReferenceType r => new ReferenceType(Substitute(r.Element, variable)),
        PointerType p => new PointerType(Substitute(p.Element, variable)),
        ArrayType a => a with { Element = Substitute(a.Element, variable) },
        _ => type,
    };
}
