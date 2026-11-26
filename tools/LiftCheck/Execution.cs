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

    public static void Check(Scan scan, string prefix, int limit, string? previous, string? baseline, string? previousLift, ulong from, ulong until)
    {
        var image = new Image(scan.Elf, scan.FileBytes);
        using var disassemblers = new ThreadLocal<Disassembly>(() => new Disassembly(), true);
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
        var added = new HashSet<ulong>();
        if (previousLift != null)
        {
            var previousSuccess = File.ReadLines(previousLift).Where(l => l.EndsWith("\t成功", StringComparison.Ordinal))
                .Select(l => ulong.Parse(l.AsSpan(0, l.IndexOf('\t')), NumberStyles.HexNumber)).ToHashSet();
            foreach (string line in File.ReadLines(prefix + ".features.local.tsv"))
            {
                var fields = line.Split('\t');
                ulong entry = ulong.Parse(fields[0], NumberStyles.HexNumber);
                if (!previousSuccess.Contains(entry) || fields[4] != "0") added.Add(entry);
            }
        }
        var executed = new HashSet<uint>();
        var observed = new HashSet<string>();
        var selected = scan.Sample(limit, SampleSeed).ToHashSet();
        var historical = previous == null ? [] : File.ReadLines(previous).Select(l => l.Split('\t'))
            .ToDictionary(r => ulong.Parse(r[0], NumberStyles.HexNumber), r => r[1]);
        var checkedEntries = new HashSet<ulong>();
        var entries = selected.Concat(tableEntries).Concat(added)
            .Concat(historical.Where(p => p.Value != "通过").Select(p => p.Key)).Where(e => e >= from && e < until).Distinct().Order();
        try
        {
            foreach (var record in entries.AsParallel().AsOrdered().WithDegreeOfParallelism(2)
                .WithMergeOptions(ParallelMergeOptions.NotBuffered).Select(Run)) Write(record);
            var candidates = File.ReadLines(prefix + ".candidates.local.tsv").Select(l => l.Split('\t')).OrderBy(r => int.Parse(r[1]));
            foreach (var row in candidates)
            {
                var entry = ulong.Parse(row[0], NumberStyles.HexNumber);
                if (entry >= from && entry < until && !checkedEntries.Contains(entry) && row[2].Split(',').Any(key => !observed.Contains(key))) Write(Run(entry));
            }
        }
        finally
        {
            foreach (var disassembly in disassemblers.Values) disassembly.Dispose();
        }

        CheckRecord Run(ulong entry)
        {
            var record = new CheckRecord(entry);
            var locations = new LiftLocations();
            using var errors = new StringWriter();
            var lift = scan.Lift(entry, locations, errors);
            if (lift.Reason == Scan.InvalidSnapshot)
            {
                record.Outcome = lift.Reason;
                record.Violation = errors.ToString();
                return record;
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
                using var emulator = new NativeRun(image, disassemblers.Value!, frame, seed, budget, words, undefined: undefined, tables: locations.Switches);
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
                    record.Undefined.Add($"{entry:x}\t{seed}\t{interpreted.Diagnostic}\t{undefined.Describe()}");
                if (reason != null)
                {
                    if (failure == null || failure == Budget) failure = reason;
                    record.Failures.Add($"{entry:x}\t{seed}\t{reason}\t{first}\t{native.Events.ElementAtOrDefault(first)}\t{interpreted.Events.ElementAtOrDefault(first)}\t{interpreted.Diagnostic ?? native.Diagnostic}");
                }
                if (!EnvironmentState.Biased(seed)) ordinary = covered.Count;
            }
            record.Edges = snapshot.Blocks.Sum(b => b.Terminator.Exits.Length);
            record.Outcome = failure ?? "通过";
            record.Covered = covered.Count;
            record.Ordinary = ordinary;
            if (tableEntries.Contains(entry))
                foreach (var (branch, table) in locations.Switches)
                    record.Items.Add($"{entry:x}\t{branch:x}\t{ordinaryItems.Count(h => h.Branch == branch)}\t{hits.Count(h => h.Branch == branch)}\t{table.Arms.Length}\t{record.Outcome}");
            record.Words = words;
            return record;
        }

        void Write(CheckRecord record)
        {
            ulong entry = record.Entry;
            checkedEntries.Add(entry);
            string group = selected.Contains(entry) ? "主核对" : tableEntries.Contains(entry) ? "跳转表核对" :
                added.Contains(entry) ? "跳转与栈分配核对" : historical.ContainsKey(entry) ? "旧入口复核" : "编码补测";
            if (record.Violation != null) violations.Write(record.Violation);
            foreach (string line in record.Failures) details.WriteLine(line);
            foreach (string line in record.Undefined) undefinedRows.WriteLine(line);
            foreach (string line in record.Items) items.WriteLine(line);
            if (selected.Contains(entry))
            {
                rows.WriteLine($"{entry:x}\t{record.Outcome}\t{record.Covered}\t{record.Edges}");
                coverage.WriteLine($"{entry:x}\t{record.Ordinary}\t{record.Covered}\t{record.Edges}");
            }
            followup.WriteLine($"{entry:x}\t{group}\t{historical.GetValueOrDefault(entry)}\t{record.Outcome}\t{record.Ordinary}\t{record.Covered}\t{record.Edges}");
            foreach (uint word in record.Words)
                if (executed.Add(word) && Decoder.Decode(word).Extension is { } key)
                {
                    observed.Add(key); witnesses.WriteLine($"{key}\t{word:x8}\t{entry:x}\t{group}\t{record.Outcome}");
                }
        }
    }

    sealed class CheckRecord(ulong entry)
    {
        public ulong Entry => entry;
        public string Outcome = "";
        public int Ordinary, Covered, Edges;
        public string? Violation;
        public List<string> Items = [], Failures = [], Undefined = [];
        public HashSet<uint> Words = [];
    }
}
