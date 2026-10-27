using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

/// <summary>按完整顶层类型生成全程序清单，供独立进程逐批恢复。</summary>
internal static class RecoveryBatches
{
    [Command("recovery-batches", "生成与 --all 同范围的恢复清单，嵌套类型不拆批", Arguments = "<binary> <metadata> <output> <batch-size>")]
    public static int Run(string binary, string metadata, string output, string batchSize)
    {
        var limit = int.Parse(batchSize);
        if (limit <= 0) throw new ArgumentOutOfRangeException(nameof(batchSize));
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var ordinary = facts.Model.Methods.Where(m => m.Address != 0 && facts.Code.RegionOf(m.Address) == CodeRegion.Managed)
            .Select(m => new RecoveryTarget(new(m, [], []), m.Address));
        var shared = facts.Model.Code.SelectMany(p => p.Value.Where(o => o.IsInstance).Select(o => new RecoveryTarget(o.Method, p.Key)))
            .Where(t => t.Instance.Method.Address == 0).GroupBy(t => t.Instance.Method)
            .Select(g => g.OrderBy(t => t.Instance.TypeArguments.Concat(t.Instance.MethodArguments)
                .Any(a => !ManagedTypes.IsReferenceType(a) || FieldLayouts.IsFullyShared(a))).ThenBy(t => t.Entry).First());
        var selected = ordinary.Concat(shared).ToArray();
        if (selected.Select(t => t.Instance.Method).Distinct().Count() != selected.Length)
            throw new InvalidDataException("同一方法定义被选择多次");
        var batches = new List<List<RecoveryTarget>>();
        foreach (var group in selected.GroupBy(t => Top(t.Instance.Method.Owner))
            .OrderBy(g => g.Key.Assembly, StringComparer.Ordinal).ThenBy(g => g.Key.Index))
        {
            if (batches.Count == 0 || batches[^1].Count + group.Count() > limit) batches.Add([]);
            batches[^1].AddRange(group.OrderBy(t => t.Instance.Method.Index));
        }
        Directory.CreateDirectory(output);
        using var manifest = new StreamWriter(Path.Combine(output, "batches.tsv"));
        manifest.WriteLine("batch\tmethods\ttop-types\tlist");
        using var inventory = new StreamWriter(Path.Combine(output, "methods.tsv"));
        inventory.WriteLine("batch\tdefinition\tentry\tmethod\tassembly\ttop-type");
        for (var i = 0; i < batches.Count; i++)
        {
            var batch = batches[i];
            var name = $"methods-{i:D3}.tsv";
            using var writer = new StreamWriter(Path.Combine(output, name));
            foreach (var target in batch)
            {
                if (RecoveryTarget.Find(facts, target.Entry, target.Instance.ToString()).Instance.Method != target.Instance.Method)
                    throw new InvalidDataException($"清单回读身份不一致：{target.Instance}");
                writer.WriteLine($"0x{target.Entry:x}\t{target.Instance}");
                inventory.WriteLine($"{i}\t{target.Instance.Method.Index}\t0x{target.Entry:x}\t{target.Instance}\t{target.Instance.Method.Owner.Assembly}\t{Top(target.Instance.Method.Owner).FullName}");
            }
            manifest.WriteLine($"{i}\t{batch.Count}\t{batch.Select(t => Top(t.Instance.Method.Owner)).Distinct().Count()}\t{name}");
        }
        Console.WriteLine($"{selected.Length} 个方法定义，{batches.Count} 批；最大批次 {batches.Max(b => b.Count)} 个方法；清单身份已回读核对");
        return 0;
    }

    private static TypeDef Top(TypeDef type)
    {
        while (type.DeclaringType is not null) type = type.DeclaringType;
        return type;
    }
}
