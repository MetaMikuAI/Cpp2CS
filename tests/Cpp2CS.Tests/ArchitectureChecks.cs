using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Xml.Linq;

namespace Cpp2CS.Tests;

internal static class ArchitectureChecks
{
    // docs/实施.md 第 1.2 节；装配方向为 Cli → Pipeline，避免双向引用。
    private static readonly IReadOnlyDictionary<string, string[]> Allowed = new Dictionary<string, string[]>
    {
        ["Model"] = [],
        ["Native"] = ["Model"],
        ["Targets.Elf"] = ["Native", "Model"],
        ["Targets.Pe"] = ["Native", "Model"],
        ["Targets.Arm64"] = ["Native", "Model"],
        ["Targets.X64"] = ["Native", "Model"],
        ["Runtime"] = ["Native", "Model"],
        ["Managed"] = ["Model"],
        ["Kernel"] = ["Native", "Runtime", "Managed", "Model"],
        ["Recovery"] = ["Kernel", "Native", "Runtime", "Managed", "Model"],
        ["Input"] = ["Native", "Runtime", "Model"],
        ["Output"] = ["Managed", "Model"],
        ["Pipeline"] = ["Model", "Native", "Targets.Elf", "Targets.Pe", "Targets.Arm64", "Targets.X64",
            "Runtime", "Kernel", "Recovery", "Managed", "Input", "Output"],
        ["Cli"] = ["Model", "Native", "Targets.Elf", "Targets.Pe", "Targets.Arm64", "Targets.X64",
            "Runtime", "Kernel", "Recovery", "Managed", "Input", "Output", "Pipeline"],
    };

    private static readonly string[] TargetIndependent =
        ["Kernel", "Recovery", "Output", "Managed", "Model", "Native", "Runtime"];

    public static int Run()
    {
        var checks = new Assertions();
        var root = FindRoot();
        var projects = Allowed.Keys.ToDictionary(name => name,
            name => Path.Combine(root, "src", $"Cpp2CS.{name}", $"Cpp2CS.{name}.csproj"));
        var byPath = projects.ToDictionary(pair => Path.GetFullPath(pair.Value), pair => pair.Key);
        var projectGraph = Allowed.Keys.ToDictionary(name => name, _ => new List<string>());
        foreach (var file in Directory.EnumerateFiles(Path.Combine(root, "src"), "*.csproj", SearchOption.AllDirectories))
            checks.True(byPath.ContainsKey(Path.GetFullPath(file)), $"未登记的工程：{Path.GetRelativePath(root, file)}");

        foreach (var (name, file) in projects)
        {
            checks.True(File.Exists(file), $"缺少工程：{file}");
            if (!File.Exists(file)) continue;
            foreach (var reference in XDocument.Load(file).Descendants().Where(e => e.Name.LocalName == "ProjectReference"))
            {
                var include = (string?)reference.Attribute("Include");
                checks.True(!string.IsNullOrWhiteSpace(include), $"{name}：ProjectReference 缺少 Include");
                if (string.IsNullOrWhiteSpace(include)) continue;
                var targetPath = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(file)!, include.Replace('\\', '/')));
                var known = byPath.TryGetValue(targetPath, out var target);
                checks.True(known, $"项目引用未登记：{name} → {include}");
                if (known) projectGraph[name].Add(target!);
            }
        }
        CheckGraph(checks, "项目引用", projectGraph);

        var assemblyGraph = Allowed.Keys.ToDictionary(name => name, _ => new List<string>());
        foreach (var name in Allowed.Keys)
        {
            // 测试工程引用全部产品工程，扫描本次构建复制到运行目录的产物。
            var file = Path.Combine(AppContext.BaseDirectory, $"Cpp2CS.{name}.dll");
            checks.True(File.Exists(file), $"缺少程序集：{file}");
            if (!File.Exists(file)) continue;
            using var stream = File.OpenRead(file);
            using var pe = new PEReader(stream);
            var metadata = pe.GetMetadataReader();
            checks.True(metadata.GetString(metadata.GetAssemblyDefinition().Name) == $"Cpp2CS.{name}",
                $"程序集身份不符：{file}");
            foreach (var handle in metadata.AssemblyReferences)
            {
                var target = metadata.GetString(metadata.GetAssemblyReference(handle).Name);
                if (!target.StartsWith("Cpp2CS.", StringComparison.Ordinal)) continue;
                assemblyGraph[name].Add(target[7..]);
            }
        }
        CheckGraph(checks, "程序集引用", assemblyGraph);
        return checks.Finish("架构边界");
    }

    private static void CheckGraph(Assertions checks, string kind, Dictionary<string, List<string>> graph)
    {
        foreach (var (source, targets) in graph)
            foreach (var target in targets)
                checks.True(Allowed[source].Contains(target), $"{kind}越界：{source} → {target}");

        foreach (var source in TargetIndependent)
        {
            var visited = new HashSet<string> { source };
            var queue = new Queue<string[]>();
            queue.Enqueue([source]);
            while (queue.TryDequeue(out var path))
            {
                if (!graph.TryGetValue(path[^1], out var targets)) continue;
                foreach (var target in targets)
                {
                    string[] next = [.. path, target];
                    checks.True(!target.StartsWith("Targets.", StringComparison.Ordinal),
                        $"{kind}目标层依赖：{string.Join(" → ", next)}");
                    if (visited.Add(target)) queue.Enqueue(next);
                }
            }
        }
    }

    private static string FindRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory); directory is not null; directory = directory.Parent)
            if (File.Exists(Path.Combine(directory.FullName, "Cpp2CS.slnx"))) return directory.FullName;
        throw new DirectoryNotFoundException("找不到 Cpp2CS.slnx；请在仓库内运行架构检查。");
    }
}
