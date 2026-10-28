namespace Cpp2CS.Tests;

/// <summary>同一类型清单可验证平铺或项目布局的实际导出文件。</summary>
internal sealed record ScopeSource(string Assembly, string Type, string Path, string Name)
{
    public static ScopeSource[] Read(string inventory, string output) => File.ReadLines(System.IO.Path.Combine(inventory, "types.tsv"))
        .Skip(1).Select(line => Resolve(line.Split('\t'), output)).ToArray();

    private static ScopeSource Resolve(string[] fields, string output)
    {
        var parts = fields[1].Split(".dll_", 2, StringSplitOptions.None);
        var assembly = parts[0];
        var type = System.IO.Path.GetFileNameWithoutExtension(parts[1]);
        var path = System.IO.Path.Combine(output, "src", fields[1]);
        if (!File.Exists(path))
        {
            var arity = type.IndexOf('`');
            if (arity >= 0) type = type[..arity];
            var last = type.LastIndexOf('.');
            path = System.IO.Path.Combine(output, "src", assembly + ".dll", last < 0 ? "" : type[..last], type[(last + 1)..] + ".cs");
        }
        if (!File.Exists(path)) throw new FileNotFoundException("目标类型源码未导出", path);
        return new(assembly, fields[0], path, type);
    }
}
