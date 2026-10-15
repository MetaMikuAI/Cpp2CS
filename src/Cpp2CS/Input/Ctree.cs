using System.Text.Json;
using Cpp2CS.Metadata;

namespace Cpp2CS.Input;

public sealed record NativeType(string Name, ulong Bytes, string Kind, bool Signed, string? Pointee);
public sealed record Variable(int Id, string Name, NativeType NativeType, bool Argument);
public sealed record Node(JsonElement Data)
{
    public int Id => Int("id");
    public string Op => Text("op");
    public string Address => Text("ea");
    public int Int(string name) => Data.GetProperty(name).GetInt32();
    public string Text(string name) => Data.GetProperty(name).GetString()!;
    public int[] List(string name) => Data.GetProperty(name).EnumerateArray().Select(x => x.GetInt32()).ToArray();
    public NativeType Type => Data.GetProperty("nativeType").Deserialize<NativeType>(Catalog.Json)!;
}

public sealed class Ctree
{
    public Dictionary<int, Node> Nodes { get; }
    public Variable[] Variables { get; }
    public int[] Arguments { get; }
    public int Root { get; }
    public string Path { get; }
    public Ctree(string path, Catalog catalog, Method method)
    {
        Path = path;
        var document = JsonDocument.Parse(File.ReadAllText(path)).RootElement;
        if (!document.GetProperty("decompiled").GetBoolean() ||
            !document.GetProperty("input_sha256").GetString()!.Equals(catalog.BinarySha256, StringComparison.OrdinalIgnoreCase) ||
            !document.GetProperty("address").GetString()!.Equals(method.Address, StringComparison.OrdinalIgnoreCase) ||
            document.GetProperty("prototype_applied").GetString() != method.NativePrototype)
            throw new InvalidOperationException($"ctree 来源与元数据不匹配: {path}");
        // 首组只接纳无警告方法；扩大范围前须分类处理每类警告。
        if (document.GetProperty("warnings").GetArrayLength() != 0)
            throw new NotSupportedException($"IDA 警告尚未裁定: {path}");
        var tree = document.GetProperty("structured");
        if (tree.GetProperty("schema").GetInt32() != 1) throw new NotSupportedException("ctree schema");
        Nodes = tree.GetProperty("nodes").EnumerateArray().Select(x => new Node(x.Clone())).ToDictionary(x => x.Id);
        Variables = tree.GetProperty("variables").Deserialize<Variable[]>(Catalog.Json)!;
        Arguments = tree.GetProperty("arguments").Deserialize<int[]>()!;
        Root = tree.GetProperty("root").GetInt32();
        if (!Nodes.ContainsKey(Root) || Nodes.Keys.Any(k => k < 0)) throw new InvalidOperationException("无效根节点或索引");
    }
    public Node this[int id] => Nodes[id];
}
