using System.Globalization;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

internal static class Execution
{
    public const int SampleSeed = 202211;
    const string Budget = "预算内一致";

    internal static string? Compare(Trace native, Trace interpreted, out int first)
    {
        first = 0;
        int common = Math.Min(native.Events.Count, interpreted.Events.Count);
        while (first < common && interpreted.Events[first].Matches(native.Events[first])) first++;
        if (first < common) return native.Events[first].Kind + "事件不符";
        if (interpreted.Error != null || native.Error != null) return interpreted.Error ?? native.Error;
        if (native.Events.Count != interpreted.Events.Count) return "序列长度事件不符";
        if (native.Exhausted != interpreted.Exhausted) return "预算边界不符";
        return native.Exhausted ? Budget : null;
    }

    public static void Inspect(Scan scan, string prefix, ulong entry, ulong seed)
    {
        var image = new Image(scan.Elf, scan.FileBytes);
        using var disassembly = new Disassembly();
        var locations = new LiftLocations();
        var snapshot = scan.Target.Lift(entry, locations).Snapshot ?? throw new InvalidDataException("入口没有快照");
        var interpreted = new Interpreter(image, seed, []).Run(snapshot, locations);
        using var output = new StreamWriter(prefix + ".trace.local.tsv");
        using var emulator = new NativeRun(image, disassembly, scan.Target.Unwind.Find(entry)!.Value, seed,
            interpreted.Exhausted ? interpreted.Instructions : EnvironmentState.StepLimit, [], output, tables: locations.Switches);
        var native = emulator.Run(entry);
        var reason = Compare(native, interpreted, out int first);
        output.WriteLine($"结论\t{reason ?? "通过"}\t{first}\t{interpreted.Diagnostic ?? native.Diagnostic}");
        for (int j = Math.Max(0, first - 8); j < Math.Min(first + 8, Math.Max(native.Events.Count, interpreted.Events.Count)); j++)
            output.WriteLine($"{j}\t{native.Events.ElementAtOrDefault(j)}\t{interpreted.Events.ElementAtOrDefault(j)}");
    }

    public static void Check(Scan scan, string prefix, int limit, string? previous, string? baseline)
    {
        var image = new Image(scan.Elf, scan.FileBytes);
        using var disassembly = new Disassembly();
        using var rows = new StreamWriter(prefix + ".execution.local.tsv");
        using var details = new StreamWriter(prefix + ".failures.local.tsv");
        using var coverage = new StreamWriter(prefix + ".coverage.local.tsv");
        using var followup = new StreamWriter(prefix + ".followup.local.tsv");
        using var undefinedRows = new StreamWriter(prefix + ".undefined.local.tsv");
        using var witnesses = new StreamWriter(prefix + ".executed.local.tsv");
        using var violations = new StreamWriter(prefix + ".check-violations.local.tsv");
        using var items = new StreamWriter(prefix + ".items.local.tsv");
        var tableEntries = File.ReadLines(prefix + ".switches.local.tsv")
            .Select(l => l.Split('\t')).Where(r => r[3] == "成功")
            .Select(r => ulong.Parse(r[0], NumberStyles.HexNumber)).ToHashSet();
        if (baseline != null)
            foreach (var line in File.ReadLines(baseline))
                if (line.EndsWith("\t成功", StringComparison.Ordinal))
                    tableEntries.Remove(ulong.Parse(line.AsSpan(0, line.IndexOf('\t')), NumberStyles.HexNumber));
        var executed = new HashSet<uint>();
        var observed = new HashSet<string>();
        var selected = scan.Sample(limit, SampleSeed).ToHashSet();
        var historical = previous == null ? [] : File.ReadLines(previous).Select(l => l.Split('\t'))
            .ToDictionary(r => ulong.Parse(r[0], NumberStyles.HexNumber), r => r[1]);
        var checkedEntries = new HashSet<ulong>();
        foreach (ulong entry in selected.Concat(tableEntries).Concat(historical.Where(p => p.Value != "通过").Select(p => p.Key)).Distinct().Order()) Run(entry);
        var candidates = File.ReadLines(prefix + ".candidates.local.tsv").Select(l => l.Split('\t')).OrderBy(r => int.Parse(r[1]));
        foreach (var row in candidates)
        {
            var entry = ulong.Parse(row[0], NumberStyles.HexNumber);
            if (row[2].Split(',').Any(key => !observed.Contains(key)) && !checkedEntries.Contains(entry)) Run(entry);
        }

        void Run(ulong entry)
        {
            checkedEntries.Add(entry);
            var locations = new LiftLocations();
            string group = selected.Contains(entry) ? "主核对" : tableEntries.Contains(entry) ? "跳转表核对" : historical.ContainsKey(entry) ? "旧入口复核" : "编码补测";
            var lift = scan.Lift(entry, locations, violations);
            if (lift.Reason == Scan.InvalidSnapshot)
            {
                if (selected.Contains(entry)) rows.WriteLine($"{entry:x}\t{lift.Reason}\t0\t0");
                followup.WriteLine($"{entry:x}\t{group}\t{historical.GetValueOrDefault(entry)}\t{lift.Reason}\t0\t0\t0");
                return;
            }
            var snapshot = lift.Snapshot ?? throw new InvalidDataException($"清单与提升结果不同 0x{entry:x}");
            var hits = new HashSet<(ulong Branch, int Item)>();
            var ordinaryItems = new HashSet<(ulong Branch, int Item)>();
            var covered = new HashSet<EdgeId>();
            var frame = scan.Target.Unwind.Find(entry)!.Value;
            string? failure = null;
            int ordinary = 0;
            var words = new HashSet<uint>();
            foreach (ulong seed in tableEntries.Contains(entry) ? EnvironmentState.TableSeeds : EnvironmentState.Seeds)
            {
                var interpreted = new Interpreter(image, seed, covered).Run(snapshot, locations);
                int budget = interpreted.Exhausted ? interpreted.Instructions : EnvironmentState.StepLimit;
                var undefined = interpreted.Error == "依赖未定义" ? new UndefinedSource(interpreted) : null;
                using var emulator = new NativeRun(image, disassembly, frame, seed, budget, words, undefined: undefined, tables: locations.Switches);
                var native = emulator.Run(entry);
                string? reason = Compare(native, interpreted, out int first);
                if (locations.Switches.Count != 0)
                    for (int j = 0; j < first; j++)
                        if (native.Events[j] is { Kind: "表项" } item)
                        {
                            hits.Add((item.Address, item.Width));
                            if (!EnvironmentState.Biased(seed)) ordinaryItems.Add((item.Address, item.Width));
                        }
                if (reason == "依赖未定义" && undefined != null)
                    undefinedRows.WriteLine($"{entry:x}\t{seed}\t{interpreted.Diagnostic}\t{undefined.Describe()}");
                if (reason != null)
                {
                    if (failure == null || failure == Budget) failure = reason;
                    details.WriteLine($"{entry:x}\t{seed}\t{reason}\t{first}\t{native.Events.ElementAtOrDefault(first)}\t{interpreted.Events.ElementAtOrDefault(first)}\t{interpreted.Diagnostic ?? native.Diagnostic}");
                }
                if (!EnvironmentState.Biased(seed)) ordinary = covered.Count;
            }
            int edges = snapshot.Blocks.Sum(b => b.Terminator.Exits.Length);
            var outcome = failure ?? "通过";
            if (selected.Contains(entry))
            {
                rows.WriteLine($"{entry:x}\t{outcome}\t{covered.Count}\t{edges}");
                coverage.WriteLine($"{entry:x}\t{ordinary}\t{covered.Count}\t{edges}");
            }
            if (tableEntries.Contains(entry))
                foreach (var (branch, table) in locations.Switches)
                    items.WriteLine($"{entry:x}\t{branch:x}\t{ordinaryItems.Count(h => h.Branch == branch)}\t{hits.Count(h => h.Branch == branch)}\t{table.Arms.Length}\t{outcome}");
            followup.WriteLine($"{entry:x}\t{group}\t{historical.GetValueOrDefault(entry)}\t{outcome}\t{ordinary}\t{covered.Count}\t{edges}");
            foreach (uint word in words)
            {
                if (executed.Add(word) && Decoder.Decode(word).Extension is { } key)
                {
                    observed.Add(key); witnesses.WriteLine($"{key}\t{word:x8}\t{entry:x}\t{group}\t{outcome}");
                }
            }
        }
    }
}
