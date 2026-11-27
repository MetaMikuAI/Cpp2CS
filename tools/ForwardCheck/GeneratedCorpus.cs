using Cpp2CS.Input;

namespace Cpp2CS.Tools.ForwardCheck;

internal sealed partial class Emit
{
    public bool RunGenerated(string destination, Il2CppInput input, int equivalent, int crossPairs)
    {
        Directory.CreateDirectory(destination);
        if (PhysicalPath(new(destination)) == PhysicalPath(new(assemblies)))
            throw new InvalidDataException("生成目录与真值程序集目录相同");
        // 结构对照的输入只有原生登记、全局元数据和实体编号，方法体集合为空。
        using (var schema = new AssemblySet())
        {
            schema.Generate(input, new Cpp2CS.Facts.ModelMetadata(metadata.Facts.Keys), []);
            CorpusAssemblyComparison.Compare(metadata, schema.Reader);
        }
        int firstMethod = methods, firstPair = pairs;
        using var generated = new AssemblySet();
        generated.Generate(input, metadata.Facts, Cases.Select(c => c.Input));
        foreach (var c in Cases)
        {
            var (module, token) = generated.Host(c.Input.Host.Entity);
            var (body, tokens, _) = generated.Reader.GeneratedBody(module, token, c.Input);
            CompareCase(c, body, tokens);
        }
        Console.WriteLine($"生成程序集 {generated.Count} 个，签名解码 {generated.Reader.DecodedMethods} 个；回读等价 {methods-firstMethod}/{equivalent}，交叉反驳 {pairs-firstPair}/{crossPairs}");
        foreach (var p in input.AssemblyMetadata.Value.UnknownParameterDefaults)
            Console.WriteLine($"元数据洞 方法 {p.Key.Method} 参数 {p.Key.Sequence}：{p.Value}");
        if (methods-firstMethod != equivalent || pairs-firstPair != crossPairs) return false;
        generated.Publish(destination);
        return true;
    }
}
