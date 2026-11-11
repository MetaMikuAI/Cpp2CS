using Mono.Cecil;

namespace Cpp2CS.Tests.Metrics;

/// <summary>原始元数据差异；不把执行比较的按需口径用于普查。</summary>
internal static class TypeMetadataAudit
{
    internal sealed record Difference(string Assembly, string Type, string Kind, string Reference, string Tested)
    {
        public bool IsValueType { get; init; }
        public int InstanceFields { get; init; }
    }
    internal static IEnumerable<Difference> Compare(ModuleDefinition reference, ModuleDefinition tested)
    {
        var candidates = tested.GetTypes().ToDictionary(t => t.FullName);
        foreach (var l in reference.GetTypes())
        {
            if (!candidates.TryGetValue(l.FullName, out var r))
            { yield return new(reference.Name, l.FullName, "TypeMissing", l.FullName, ""); continue; }
            var rows = new (string Kind, string L, string R)[] {
                ("Attributes", l.Attributes.ToString(), r.Attributes.ToString()),
                ("Base", l.BaseType?.FullName ?? "", r.BaseType?.FullName ?? ""),
                ("Layout", $"{l.PackingSize}:{l.ClassSize}", $"{r.PackingSize}:{r.ClassSize}"),
                ("Fields", string.Join("\n", l.Fields.Select(Field)), string.Join("\n", r.Fields.Select(Field))),
                ("Methods", string.Join("\n", l.Methods.Select(m => m.FullName)), string.Join("\n", r.Methods.Select(m => m.FullName))) };
            foreach (var row in rows.Where(row => row.L != row.R))
                yield return new(reference.Name, l.FullName, row.Kind, row.L, row.R)
                { IsValueType = l.IsValueType, InstanceFields = l.Fields.Count(f => !f.IsStatic) };
        }
    }
    private static string Field(FieldDefinition f) => $"{f.Attributes}:{f.FieldType.FullName}:{f.Name}:offset={f.Offset}";
    public const string Command = "type-metadata-audit";
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        if (corpus is null) { Console.WriteLine("跳过类型差异普查：未设置 CPP2CS_CORPUS。"); return 0; }
        var output = Path.Combine(ArchitectureChecks.FindRoot(), "artifacts", "pipeline-corpus.local.output");
        var differences = new List<Difference>();
        foreach (var path in Directory.GetFiles(Path.Combine(corpus, "artifacts", "ManagedStripped"), "*.dll").Order())
        {
            using var reference = ModuleDefinition.ReadModule(path);
            using var tested = ModuleDefinition.ReadModule(Path.Combine(output, Path.GetFileName(path)));
            differences.AddRange(Compare(reference, tested));
        }
        File.WriteAllText(Path.Combine(output, "types.local.json"), IlMetrics.Json(differences));
        foreach (var group in differences.GroupBy(d => d.Kind)) Console.WriteLine($"{group.Key}: {group.Count()}");
        return 0;
    }
}
