using Cpp2CS.Tests.Architecture;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Cpp2CS.Tests;

/// <summary>
/// 结构检查（G0）：按实际符号引用检查模块边界（别名、完整类型名、var 与目标类型的 new() 适用相同规则）；
/// 语义计数与棘轮、访问白名单与豁免清单、族归属快照、注册表快照与洞编码清单（账本见 tests/Cpp2CS.Tests/Architecture）。
/// --write：棘轮写回下降值并删除已无访问的白名单与豁免条目（不会上调或新增）；--write-snapshots：按代码重写族归属、注册表与洞编码快照；
/// --bootstrap：账本不存在时按现状建立初值；--milestone MSn：检查到期条目已删除。
/// </summary>
internal static class ArchitectureCheck
{
    [Command("architecture", "检查依赖方向、语义计数棘轮、白名单与豁免清单、族归属与注册表快照、洞编码清单", Arguments = "<repository> [--write] [--write-snapshots] [--bootstrap] [--milestone MSn] [--deps]")]
    public static int Run(string repository, string[] options)
    {
        var known = new[] { "--write", "--write-snapshots", "--bootstrap", "--deps" };
        string? milestone = null;
        string? baseRevision = null;
        for (var i = 0; i < options.Length; i++)
        {
            if (options[i] == "--milestone" && i + 1 < options.Length) milestone = options[++i];
            else if (options[i] == "--base" && i + 1 < options.Length) baseRevision = options[++i];
            else if (!known.Contains(options[i])) throw new ArgumentException($"未知参数 {options[i]}");
        }
        var model = SourceModel.Load(repository);
        if (options.Contains("--deps")) return Dependencies(model);
        var failures = new List<string>();
        var layers = Layers(model);
        failures.AddRange(layers);

        var census = new StructureCensus(model);
        var registry = Ledgers.Registry();
        var accesses = census.Accesses.Concat(Ledgers.DuplicateOrders(registry)).Concat(Ledgers.DuplicatePasses(census.PassNames)).ToList();
        var folder = Ledgers.Folder(model.Repository);
        var paths = new
        {
            Ratchet = Path.Combine(folder, "ratchet.tsv"),
            Whitelist = Path.Combine(folder, "whitelist.tsv"),
            Exemptions = Path.Combine(folder, "exemptions.tsv"),
            Families = Path.Combine(folder, "families.tsv"),
            Registry = Path.Combine(folder, "registry.tsv"),
            HoleCodes = Path.Combine(folder, "hole-codes.tsv"),
            SharedBodies = Path.Combine(folder, "shared-step-bodies.tsv"),
            Transfers = Path.Combine(folder, "transfers.tsv"),
        };
        var holeCodes = Ledgers.HoleCodes(census.HoleCodes);
        if (options.Contains("--bootstrap"))
        {
            if (new[] { paths.Ratchet, paths.Whitelist, paths.Exemptions, paths.Families, paths.Registry, paths.HoleCodes }.Any(File.Exists))
                throw new IOException("账本已存在；--bootstrap 只用于建立初值");
            Directory.CreateDirectory(folder);
            var entries = accesses.GroupBy(a => (a.Tag, a.Member, a.File)).Select(g =>
            {
                var (package, expiry) = Ledgers.Schedule(g.First());
                return new Ledgers.Entry(g.Key.Tag, g.Key.Member, g.Key.File, package, expiry, "V2 建立时的现有访问");
            }).ToList();
            Ledgers.WriteEntries(paths.Whitelist, entries.Where(e => !Ledgers.IsExemption(e.Tag)));
            Ledgers.WriteEntries(paths.Exemptions, entries.Where(e => Ledgers.IsExemption(e.Tag)));
            Ledgers.WriteEntries(paths.SharedBodies, []);
            WriteSnapshots(model, registry, holeCodes, paths.Families, paths.Registry, paths.HoleCodes);
            Ledgers.WriteRatchet(paths.Ratchet, Counts(census, Ledgers.ReadEntries(paths.Whitelist), Ledgers.ReadEntries(paths.Exemptions)));
            Console.WriteLine($"已建立账本：白名单 {entries.Count(e => !Ledgers.IsExemption(e.Tag))} 条，豁免 {entries.Count(e => Ledgers.IsExemption(e.Tag))} 条");
        }
        var whitelist = Ledgers.ReadEntries(paths.Whitelist);
        var exemptions = Ledgers.ReadEntries(paths.Exemptions);
        // 共享步骤体（I3）：登记的调用点长期放行，不到期；登记表中的调用点数纳入棘轮
        var sharedBodies = Ledgers.ReadEntries(paths.SharedBodies);
        var registered = accesses.Where(a => a.Tag == "I3" && sharedBodies.Any(e => e.Covers(a))).ToList();
        accesses = accesses.Except(registered).ToList();
        if (options.Contains("--write"))
        {
            whitelist = whitelist.Where(e => accesses.Any(e.Covers)).ToList();
            exemptions = exemptions.Where(e => accesses.Any(e.Covers)).ToList();
            Ledgers.WriteEntries(paths.Whitelist, whitelist);
            Ledgers.WriteEntries(paths.Exemptions, exemptions);
            var recorded = Ledgers.ReadRatchet(paths.Ratchet);
            // 只写回下降；给出 --base 时，被本次新增转移条目覆盖的上升也写回（覆盖与源键下降由下面的 CheckRises 核对）
            var covered = new Dictionary<string, int>(StringComparer.Ordinal);
            if (baseRevision is not null && File.Exists(paths.Transfers))
            {
                var baseTransfers = Ledgers.ReadTransfers(Git(model.Repository, "show", $"{baseRevision}:{Path.GetRelativePath(model.Repository, paths.Transfers).Replace('\\', '/')}"));
                foreach (var transfer in Ledgers.ReadTransfers(File.ReadLines(paths.Transfers)).Where(t => !baseTransfers.Contains(t)))
                    covered[transfer.Target] = covered.GetValueOrDefault(transfer.Target) + transfer.Count;
            }
            var lowered = new SortedDictionary<string, int>(StringComparer.Ordinal);
            foreach (var (key, value) in Counts(census, whitelist, exemptions))
                lowered[key] = Math.Min(value, recorded.TryGetValue(key, out var was) ? was + covered.GetValueOrDefault(key) : covered.TryGetValue(key, out var rise) ? rise : value);
            foreach (var (key, value) in recorded.Where(p => !lowered.ContainsKey(p.Key))) lowered[key] = 0;
            Ledgers.WriteRatchet(paths.Ratchet, lowered.Where(p => p.Value > 0 || recorded.ContainsKey(p.Key) && recorded[p.Key] == 0).ToDictionary());
        }
        if (options.Contains("--write-snapshots")) WriteSnapshots(model, registry, holeCodes, paths.Families, paths.Registry, paths.HoleCodes);

        var counts = Counts(census, whitelist, exemptions);
        Ledgers.CheckEntries("白名单", whitelist, accesses.Where(a => !Ledgers.IsExemption(a.Tag)).ToList(), milestone, failures);
        Ledgers.CheckEntries("豁免清单", exemptions, accesses.Where(a => Ledgers.IsExemption(a.Tag)).ToList(), milestone, failures);
        Ledgers.CheckEntries("共享步骤体登记表", sharedBodies, registered, null, failures);
        if (registered.Count > 0) counts["shared-step-body-call-sites/I3"] = registered.Count;
        Ledgers.CheckRatchet(Ledgers.ReadRatchet(paths.Ratchet), counts, failures);
        var transfers = File.Exists(paths.Transfers) ? Ledgers.ReadTransfers(File.ReadLines(paths.Transfers)) : [];
        Ledgers.CheckTransfers(transfers, census.MethodScopes, failures);
        if (baseRevision is not null)
        {
            string[] Show(string path) => Git(model.Repository, "show", $"{baseRevision}:{Path.GetRelativePath(model.Repository, path).Replace('\\', '/')}");
            var baseline = new SortedDictionary<string, int>(Ledgers.ReadRatchetLines(Show(paths.Ratchet)), StringComparer.Ordinal);
            Ledgers.CheckRises(baseline, Ledgers.ReadRatchet(paths.Ratchet), Ledgers.ReadTransfers(Show(paths.Transfers)), transfers, failures);
        }
        Ledgers.CheckPairs("族归属快照", Ledgers.ReadPairs(paths.Families), Ledgers.CurrentFamilies(model), failures);
        Ledgers.CheckPairs("注册表快照", RegistryPairs(File.ReadLines(paths.Registry)), RegistryPairs(Ledgers.RegistryLines(registry)), failures);
        Ledgers.CheckPairs("洞编码清单", HoleCodeRows(paths.HoleCodes).ToDictionary(p => p.Key, p => p.Value.Counts), holeCodes, failures);

        foreach (var failure in failures) Console.WriteLine($"✗ {failure}");
        Console.WriteLine($"architecture：越层引用 {layers.Count}；计数项 {counts.Count}；白名单 {whitelist.Count} 条，豁免 {exemptions.Count} 条；失败 {failures.Count} 项");
        return failures.Count == 0 ? 0 : 1;
    }

    /// <summary>读取基准提交中的文件；文件在该提交中不存在时为空。</summary>
    private static string[] Git(string repository, params string[] arguments)
    {
        var start = new System.Diagnostics.ProcessStartInfo("git") { WorkingDirectory = repository, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = System.Diagnostics.Process.Start(start)!;
        var output = process.StandardOutput.ReadToEnd();
        process.WaitForExit();
        return process.ExitCode == 0 ? output.Split('\n') : [];
    }

    private static SortedDictionary<string, int> Counts(StructureCensus census, IEnumerable<Ledgers.Entry> whitelist, IEnumerable<Ledgers.Entry> exemptions)
    {
        var counts = new SortedDictionary<string, int>(census.Counts, StringComparer.Ordinal);
        foreach (var group in whitelist.GroupBy(e => e.Tag)) counts[$"whitelist-entries/{group.Key}"] = group.Count();
        foreach (var group in exemptions.GroupBy(e => e.Tag)) counts[$"exemption-entries/{group.Key}"] = group.Count();
        return counts;
    }

    private static Dictionary<string, string> RegistryPairs(IEnumerable<string> lines) => lines.Where(l => l.Length > 0 && !l.StartsWith('#'))
        .Select(l => l.Split('\t')).ToDictionary(f => $"{f[0]}\t{f[1]}\t{f[5]}", f => $"Order={f[2]} After={f[3]} Invalidates={f[4]}");

    private static void WriteSnapshots(SourceModel model, List<Ledgers.Registration> registry, SortedDictionary<string, string> holeCodes,
        string families, string registryPath, string holeCodesPath)
    {
        Ledgers.WritePairs(families, "# 文件\t所属范围（族）。跨族目录移动文件会改变这里，提交说明须带用户确认标记（主文 3.3）。", Ledgers.CurrentFamilies(model));
        File.WriteAllLines(registryPath, Ledgers.RegistryLines(registry));
        var notes = File.Exists(holeCodesPath) ? HoleCodeRows(holeCodesPath).ToDictionary(p => p.Key, p => p.Value.Note) : [];
        File.WriteAllLines(holeCodesPath, new[] { "# rule\t次数\t所在范围\t与所在方法名不一致的次数\t说明。编码为 recovery.<rule>；新增编码先进清单（主文 4.13）。" }
            .Concat(holeCodes.Select(p => $"{p.Key}\t{p.Value}\t{notes.GetValueOrDefault(p.Key, "")}")));
    }

    /// <summary>洞编码清单的一行：前三列（次数、所在范围、与所在方法名不一致的次数）由代码决定，第四列是说明。</summary>
    private static Dictionary<string, (string Counts, string Note)> HoleCodeRows(string path) => File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#'))
        .Select(l => l.Split('\t')).ToDictionary(f => f[0], f => (string.Join('\t', f[1..4]), f.ElementAtOrDefault(4) ?? ""));

    /// <summary>命名空间依赖矩阵（诊断用）：源命名空间前两级 → 目标命名空间前两级，按引用次数。</summary>
    private static int Dependencies(SourceModel model)
    {
        var edges = new SortedDictionary<string, int>(StringComparer.Ordinal);
        foreach (var project in model.Projects.Where(p => p.Name != "Tests"))
            foreach (var (tree, source, target, _) in References(project))
            {
                static string Head(string ns) => string.Join('.', ns.Split('.').Take(2));
                if (Head(source) != Head(target)) edges[$"{Head(source)} → {Head(target)}"] = edges.GetValueOrDefault($"{Head(source)} → {Head(target)}") + 1;
            }
        foreach (var (edge, count) in edges) Console.WriteLine($"{count,6}  {edge}");
        return 0;
    }

    /// <summary>每个显式名称、var 声明与目标类型 new() 引用的类型或成员所在的命名空间。</summary>
    private static IEnumerable<(SyntaxTree Tree, string Source, string Target, (SyntaxNode Node, string Symbol) Site)> References(SourceModel.Project project)
    {
        foreach (var tree in project.Trees)
        {
            var semantic = project.Compilation.GetSemanticModel(tree);
            var root = tree.GetRoot();
            var source = root.DescendantNodes().OfType<BaseNamespaceDeclarationSyntax>().FirstOrDefault()?.Name.ToString() ?? "";
            foreach (var name in root.DescendantNodes().OfType<SimpleNameSyntax>().Where(n => !n.Ancestors().Any(a => a is UsingDirectiveSyntax)))
                if (semantic.GetSymbolInfo(name).Symbol is { } symbol)
                    yield return (tree, source, symbol.ContainingNamespace?.ToDisplayString() ?? "", (name, symbol.Name));
            foreach (var node in root.DescendantNodes().Where(n => n is ImplicitObjectCreationExpressionSyntax || n is VariableDeclarationSyntax { Type.IsVar: true }))
            {
                var type = node is VariableDeclarationSyntax declaration ? semantic.GetTypeInfo(declaration.Type).Type : semantic.GetTypeInfo(node).Type;
                if (type is not null) yield return (tree, source, type.ContainingNamespace?.ToDisplayString() ?? "", (node, type.Name));
            }
        }
    }

    private static List<string> Layers(SourceModel model)
    {
        var failures = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var project in model.Projects.Where(p => p.Name != "Tests"))
            foreach (var (tree, source, target, (node, symbol)) in References(project))
                if (Forbidden(source, target))
                    failures.Add($"越层引用 {model.Relative(tree)}:{SourceModel.Line(node)}: {source} → {target} ({symbol})");
        return failures.ToList();
    }

    private static bool Within(string name, string layer) => name == "Cpp2CS." + layer || name.StartsWith("Cpp2CS." + layer + ".", StringComparison.Ordinal);
    private static bool Forbidden(string source, string target)
    {
        if (!target.StartsWith("Cpp2CS.", StringComparison.Ordinal)) return false;
        if (Within(source, "Facts.Derived") && new[] { "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Facts") && !Within(source, "Facts.Derived") && new[] { "Machine", "Idioms", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Machine") && new[] { "Idioms", "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Idioms") && new[] { "Managed", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Managed") && new[] { "Machine", "Idioms", "Recovery" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Model") && new[] { "Facts", "Machine", "Managed", "Recovery", "Idioms" }.Any(l => Within(target, l))) return true;
        // 基础层：Image、Ir 只依赖 Model；Calls 只依赖 Ir、Managed、Model；Diagnostics 不依赖其他层；Options 只依赖 Diagnostics；Input 不依赖分析层
        if (Within(source, "Image") && new[] { "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Ir") && new[] { "Image", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Calls") && new[] { "Image", "Facts", "Machine", "Idioms", "Recovery", "Diagnostics", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Diagnostics") && new[] { "Image", "Model", "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls", "Options" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Options") && new[] { "Image", "Model", "Ir", "Facts", "Machine", "Idioms", "Managed", "Recovery", "Calls" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Input") && new[] { "Machine", "Idioms", "Managed", "Recovery", "Calls" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Output") && new[] { "Recovery", "Extensions", "Pipeline" }.Any(l => Within(target, l))) return true;
        if (Within(source, "Extensions") && Within(target, "Pipeline")) return true;
        return !new[] { "Output", "Extensions", "Input", "Pipeline", "Cli" }.Any(l => Within(source, l))
            && new[] { "Output", "Extensions", "Pipeline", "Cli" }.Any(l => Within(target, l));
    }
}
