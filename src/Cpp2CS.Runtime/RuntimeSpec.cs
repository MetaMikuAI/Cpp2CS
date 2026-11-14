using System.Collections.Frozen;
using System.Numerics;
using System.Text.Json;

namespace Cpp2CS.Runtime;

// 函数目录与操作登记表后续作为独立部分加入，布局不承担它们的职责。
public sealed class RuntimeSpec
{
    private RuntimeSpec(RuntimeLayoutSpec layout) => Layout = layout;
    public RuntimeLayoutSpec Layout { get; }
    public string? ManagedExceptionWrapperTypeName { get; private init; }

    public static RuntimeSpec Load(string path, string unityVersion, string triple, string dataModel)
    {
        using var stream = File.OpenRead(path);
        return Read(stream, path, unityVersion, triple, dataModel);
    }

    // 不猜测补丁版本，也不在不同目标之间回退。
    public static RuntimeSpec Select(string unityVersion, string triple, string dataModel)
    {
        var assembly = typeof(RuntimeSpec).Assembly;
        var matches = new List<RuntimeSpec>();
        foreach (var resource in assembly.GetManifestResourceNames().Where(n => n.StartsWith("Cpp2CS.Layouts.", StringComparison.Ordinal)))
        {
            using var stream = assembly.GetManifestResourceStream(resource)!;
            using var document = JsonDocument.Parse(stream);
            var root = document.RootElement;
            ValidateVersion(root, resource);
            if (root.GetProperty("unity_version").GetString() == unityVersion &&
                Targets(root).Any(t => Matches(t, triple, dataModel)))
                matches.Add(Parse(root, resource, unityVersion, triple, dataModel));
        }
        return matches.Count == 1 ? matches[0] : throw new InvalidDataException(
            $"嵌入布局规格：Unity={unityVersion}, target={triple}, data_model={dataModel} 匹配 {matches.Count} 份文件，要求唯一匹配。");
    }

    // 调用方保留流的所有权；对象不持有 JsonDocument 或可变集合。
    public static RuntimeSpec Read(Stream stream, string source, string unityVersion, string triple, string dataModel)
    {
        using var document = JsonDocument.Parse(stream);
        return Parse(document.RootElement, source, unityVersion, triple, dataModel);
    }

    private static void ValidateVersion(JsonElement root, string source)
    {
        if (!root.TryGetProperty("schema_version", out var version) || version.ValueKind != JsonValueKind.Number || !version.TryGetInt32(out var value) || value != 1)
            throw new InvalidDataException($"{source}：未知或缺失 schema_version：{version}。");
    }

    private static IEnumerable<JsonElement> Targets(JsonElement root) => root.TryGetProperty("targets", out var targets)
        ? targets.EnumerateArray() : [root.GetProperty("target")];
    private static bool Matches(JsonElement target, string triple, string model) =>
        target.GetProperty("triple").GetString() == triple && target.GetProperty("data_model").GetString() == model;

    private static RuntimeSpec Parse(JsonElement root, string source, string unityVersion, string triple, string dataModel)
    {
        ValidateVersion(root, source);
        var targets = Targets(root).Where(t => Matches(t, triple, dataModel)).ToArray();
        if (root.GetProperty("unity_version").GetString() != unityVersion || targets.Length != 1)
            throw new InvalidDataException($"{source}：不匹配 Unity={unityVersion}, target={triple}, data_model={dataModel}。");
        var records = root.GetProperty("records").EnumerateObject().ToFrozenDictionary(p => p.Name,
            p => new RuntimeRecord(source, p.Name, Text(p.Value, "type"), Text(p.Value, "kind"),
                Number(p.Value, "size"), Number(p.Value, "alignment"), Fields(p.Value.GetProperty("fields"), source, p.Name)), StringComparer.Ordinal);
        var primitives = targets[0].GetProperty("primitives").EnumerateObject().ToFrozenDictionary(p => p.Name,
            p => new RuntimePrimitive(Number(p.Value, "size"), Number(p.Value, "alignment")), StringComparer.Ordinal);
        var constants = root.GetProperty("constants").EnumerateObject().ToFrozenDictionary(p => p.Name,
            p => BigInteger.Parse(p.Value.GetRawText(), System.Globalization.CultureInfo.InvariantCulture), StringComparer.Ordinal);
        return new(new(source, unityVersion, triple, dataModel, records, primitives, constants))
        { ManagedExceptionWrapperTypeName = root.TryGetProperty("cxx_exception_wrapper_type", out var wrapper) ? wrapper.GetString() : null };
    }

    private static FrozenDictionary<string, RuntimeField> Fields(JsonElement fields, string source, string owner) =>
        fields.EnumerateArray().ToFrozenDictionary(f => Text(f, "name"), f =>
        {
            var name = Text(f, "name");
            var path = $"{owner}.{name}";
            return new RuntimeField(source, path, Text(f, "type"), Number(f, "offset_bits"), Number(f, "size"),
                f.TryGetProperty("bit_width", out var width) ? width.GetInt64() : null,
                f.TryGetProperty("members", out var members) ? Fields(members, source, path) : FrozenDictionary<string, RuntimeField>.Empty)
            {
                ImmutableEvidence = f.TryGetProperty("immutable", out var immutable) ? immutable.GetString() : null,
                StableAfterNonzeroEvidence = f.TryGetProperty("stable_after_nonzero", out var stable) ? stable.GetString() : null,
                ArrayElement = f.TryGetProperty("array_element", out var element)
                    ? new(Text(element, "type"), Number(element, "size"), Text(element, "immutable")) : null,
            };
        }, StringComparer.Ordinal);
    private static string Text(JsonElement value, string name) => value.GetProperty(name).GetString()
        ?? throw new InvalidDataException($"布局属性 {name} 不能为 null。");
    private static long Number(JsonElement value, string name) => value.GetProperty(name).GetInt64();
}

public sealed class RuntimeLayoutSpec
{
    internal RuntimeLayoutSpec(string source, string unityVersion, string triple, string dataModel,
        FrozenDictionary<string, RuntimeRecord> records, FrozenDictionary<string, RuntimePrimitive> primitives,
        FrozenDictionary<string, BigInteger> constants)
    {
        Source = source; UnityVersion = unityVersion; Triple = triple; DataModel = dataModel;
        Records = records; Primitives = primitives; Constants = constants;
    }
    public string Source { get; }
    public string UnityVersion { get; }
    public string Triple { get; }
    public string DataModel { get; }
    public FrozenDictionary<string, RuntimeRecord> Records { get; }
    public FrozenDictionary<string, RuntimePrimitive> Primitives { get; }
    public FrozenDictionary<string, BigInteger> Constants { get; }
    public RuntimeRecord Record(string name) => Lookup(Records, name, Source);
    public RuntimePrimitive Primitive(string name) => Lookup(Primitives, name, Source);
    public BigInteger Constant(string name) => Lookup(Constants, name, Source);
    public RuntimeField Field(string record, string field) => Record(record).Field(field);
    public long ObjectHeaderSize => Record("Il2CppObject").Size;
    public long ArrayDataStart => Field("Il2CppArraySize", "vector").ByteOffset;
    public long StringCharactersStart => Field("Il2CppString", "chars").ByteOffset;
    public long VtableStart => Field("Il2CppClass", "vtable").ByteOffset;
    public long VtableSlotSize => Record("VirtualInvokeData").Size;
    public RuntimeField VirtualCallMethodPointer => Field("VirtualInvokeData", "methodPtr");
    public RuntimeField VirtualCallMethodInfo => Field("VirtualInvokeData", "method");
    public long VtableSlotFieldOffset(long slot, string field)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(slot);
        return checked(VtableStart + slot * VtableSlotSize + Field("VirtualInvokeData", field).ByteOffset);
    }
    internal static T Lookup<T>(IReadOnlyDictionary<string, T> items, string name, string source) =>
        items.TryGetValue(name, out var value) ? value : throw new KeyNotFoundException($"{source}：缺少布局名称 '{name}'。");
}

public sealed record RuntimePrimitive(long Size, long Alignment);

public sealed class RuntimeRecord
{
    private readonly string source;
    internal RuntimeRecord(string source, string name, string type, string kind, long size, long alignment,
        FrozenDictionary<string, RuntimeField> fields)
    { this.source = source; Name = name; Type = type; Kind = kind; Size = size; Alignment = alignment; Fields = fields; }
    public string Name { get; }
    public string Type { get; }
    public string Kind { get; }
    public long Size { get; }
    public long Alignment { get; }
    public FrozenDictionary<string, RuntimeField> Fields { get; }
    public RuntimeField Field(string name) => Fields.TryGetValue(name, out var field) ? field :
        throw new KeyNotFoundException($"{source}：缺少布局字段 '{Name}.{name}'。");
}

public sealed record RuntimeArrayElement(string Type, long Size, string ImmutableEvidence);

public sealed class RuntimeField
{
    private readonly string source;
    internal RuntimeField(string source, string path, string type, long offsetBits, long size, long? bitWidth,
        FrozenDictionary<string, RuntimeField> members)
    { this.source = source; Path = path; Type = type; OffsetBits = offsetBits; Size = size; BitWidth = bitWidth; Members = members; }
    public string Path { get; }
    public string Type { get; }
    // 嵌套成员相对其直接所属结构，调用方可逐层查询。
    public long OffsetBits { get; }
    public long Size { get; }
    public long? BitWidth { get; }
    /// <summary>生成代码可见的已就绪结构上不再改写；空值表示没有此凭据。</summary>
    public string? ImmutableEvidence { get; init; }
    /// <summary>完整字段非零后不再改变；不声称空值阶段不可变。</summary>
    public string? StableAfterNonzeroEvidence { get; init; }
    public RuntimeArrayElement? ArrayElement { get; init; }
    public FrozenDictionary<string, RuntimeField> Members { get; }
    public RuntimeField Member(string name) => Members.TryGetValue(name, out var field) ? field :
        throw new KeyNotFoundException($"{source}：缺少布局字段 '{Path}.{name}'。");
    public long ByteOffset => BitWidth is null && OffsetBits % 8 == 0 ? OffsetBits / 8 :
        throw new InvalidOperationException($"{source}：'{Path}' 是位域或未按字节对齐，请查询 BitStorage。");
    // 最小覆盖字节区间，不声称它是编译器分配的完整存储单元；Size 仍为声明类型大小。
    public RuntimeBitStorage BitStorage => BitWidth is { } width
        ? new(OffsetBits / 8, OffsetBits % 8, width, checked((OffsetBits % 8 + width + 7) / 8))
        : throw new InvalidOperationException($"{source}：'{Path}' 不是位域。");
}

public sealed record RuntimeBitStorage(long ByteOffset, long BitOffset, long BitWidth, long ByteSize);
