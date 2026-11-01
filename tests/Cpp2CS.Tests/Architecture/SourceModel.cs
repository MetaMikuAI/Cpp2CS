using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Cpp2CS.Tests.Architecture;

/// <summary>
/// 仓库源码的 Roslyn 编译：每个项目一份编译，其他项目以测试程序输出目录中的程序集作为引用。
/// 路径一律相对仓库根，分隔符为“/”。
/// </summary>
internal sealed class SourceModel
{
    public sealed record Project(string Name, string Folder, CSharpCompilation Compilation, SyntaxTree[] Trees);

    private static readonly (string Name, string Folder, string Assembly)[] Layout =
    [
        ("Core", "src/Cpp2CS.Core", "Cpp2CS.Core"),
        ("Output", "src/Cpp2CS.Output", "Cpp2CS.Output"),
        ("Extensions", "src/Cpp2CS.Extensions", "Cpp2CS.Extensions"),
        ("Input", "src/Cpp2CS.Input", "Cpp2CS.Input"),
        ("Pipeline", "src/Cpp2CS.Pipeline", "Cpp2CS.Pipeline"),
        ("Cli", "src/Cpp2CS.Cli", "cpp2cs"),
        ("Tests", "tests/Cpp2CS.Tests", "Cpp2CS.Tests"),
    ];

    public string Repository { get; }
    public IReadOnlyList<Project> Projects { get; }
    public Project this[string name] => Projects.Single(p => p.Name == name);

    private SourceModel(string repository, IReadOnlyList<Project> projects) => (Repository, Projects) = (repository, projects);

    public static SourceModel Load(string repository)
    {
        repository = Path.GetFullPath(repository);
        var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
            .Concat(Directory.GetFiles(AppContext.BaseDirectory, "*.dll")).Distinct(StringComparer.OrdinalIgnoreCase)
            .Select(p => (Path: p, Reference: (MetadataReference)MetadataReference.CreateFromFile(p))).ToArray();
        var globals = CSharpSyntaxTree.ParseText("global using System; global using System.IO; global using System.Linq; global using System.Collections.Generic; global using System.Threading; global using System.Threading.Tasks;",
            new(LanguageVersion.Preview));
        var projects = Layout.Select(layout =>
        {
            var folder = Path.Combine(repository, layout.Folder);
            // Input 关闭默认编译项：只编译本目录顶层文件，另就地编译第三方 Il2CppDumper 源码（只参与绑定，不参与检查）
            var input = layout.Name == "Input";
            var trees = Directory.EnumerateFiles(folder, "*.cs", input ? SearchOption.TopDirectoryOnly : SearchOption.AllDirectories)
                .Where(p => !Path.GetRelativePath(folder, p).Split(Path.DirectorySeparatorChar).Any(s => s is "obj" or "bin"))
                .Order(StringComparer.Ordinal)
                .Select(p => CSharpSyntaxTree.ParseText(File.ReadAllText(p), new(LanguageVersion.Preview), p)).ToArray();
            var dumper = Path.Combine(repository, "third_party", "Il2CppDumper", "Il2CppDumper");
            var extra = input ? Directory.EnumerateFiles(dumper, "*.cs", SearchOption.AllDirectories)
                .Where(p => Path.GetRelativePath(dumper, p).Replace('\\', '/') is not ("Program.cs" or "Resource1.Designer.cs")
                    && !Path.GetRelativePath(dumper, p).Split(Path.DirectorySeparatorChar).Any(s => s is "obj" or "bin"))
                .Order(StringComparer.Ordinal)
                .Select(p => CSharpSyntaxTree.ParseText(File.ReadAllText(p), new(LanguageVersion.Preview), p)) : [];
            var compilation = CSharpCompilation.Create(layout.Assembly, input ? trees.Concat(extra) : trees.Append(globals),
                references.Where(r => !string.Equals(Path.GetFileNameWithoutExtension(r.Path), layout.Assembly, StringComparison.OrdinalIgnoreCase)).Select(r => r.Reference),
                new(OutputKind.DynamicallyLinkedLibrary, allowUnsafe: true));
            return new Project(layout.Name, layout.Folder, compilation, trees);
        }).ToArray();
        return new SourceModel(repository, projects);
    }

    public string Relative(SyntaxTree tree) => Path.GetRelativePath(Repository, tree.FilePath).Replace('\\', '/');

    public string Relative(Location location) => location.SourceTree is { } tree ? Relative(tree) : "";

    public static int Line(SyntaxNode node) => node.GetLocation().GetLineSpan().StartLinePosition.Line + 1;

    /// <summary>
    /// 代码所在的计数范围（族）：Recovery 的子目录为 Recovery/子目录，Recovery 根目录为 Recovery，
    /// Core 的其他代码为顶层目录名（Idioms、Machine……），其他项目为项目名。
    /// </summary>
    public static string Scope(string relative)
    {
        var parts = relative.Split('/');
        if (parts.Length >= 3 && parts[0] == "src" && parts[1] == "Cpp2CS.Core")
        {
            if (parts.Length == 3) return "Core";
            if (parts[2] == "Recovery") return parts.Length == 4 ? "Recovery" : "Recovery/" + parts[3];
            return parts[2];
        }
        if (parts.Length >= 2 && parts[0] == "src") return parts[1]["Cpp2CS.".Length..];
        if (parts.Length >= 2 && parts[0] == "tests") return "Tests";
        return "Other";
    }

    /// <summary>Recovery 下的族名（目录名）；不在族目录中的代码返回 null。</summary>
    public static string? Family(string relative) => Scope(relative) is var scope && scope.StartsWith("Recovery/", StringComparison.Ordinal) ? scope["Recovery/".Length..] : null;
}
