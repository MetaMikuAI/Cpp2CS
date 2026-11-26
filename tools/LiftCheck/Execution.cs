using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.LiftCheck;

internal static class Execution
{
    public const int SampleSeed = 202211;
    public static void Check(Scan scan, string prefix, int limit)
    {
        var image = new Image(scan.Elf, scan.FileBytes);
        using var disassembly = new Disassembly();
        using var rows = new StreamWriter(prefix + ".execution.local.tsv");
        using var details = new StreamWriter(prefix + ".failures.local.tsv");
        foreach (ulong entry in scan.Sample(limit, SampleSeed))
        {
            var result = scan.Target.Lift(entry);
            if (result.Snapshot is not { } snapshot) throw new InvalidDataException($"清单与提升结果不同 0x{entry:x}");
            var covered = new HashSet<EdgeId>();
            var frame = scan.Target.Unwind.Find(entry)!.Value;
            var reasons = new List<string>();
            foreach (ulong seed in EnvironmentState.Seeds)
            {
                var interpreted = new Interpreter(image, seed, covered).Run(snapshot);
                using var emulator = new NativeRun(image, disassembly, frame, seed);
                var native = emulator.Run(entry);
                string? reason = interpreted.Error ?? native.Error;
                int first = 0;
                while (first < Math.Min(native.Events.Count, interpreted.Events.Count) && native.Events[first] == interpreted.Events[first]) first++;
                if (reason == null && (first != native.Events.Count || first != interpreted.Events.Count))
                {
                    string kind = first < native.Events.Count ? native.Events[first].Kind : "序列长度";
                    reason = kind + "事件不符";
                }
                if (reason != null)
                {
                    reasons.Add(reason);
                    details.WriteLine($"{entry:x}\t{seed}\t{reason}\t{first}\t{native.Events.ElementAtOrDefault(first)}\t{interpreted.Events.ElementAtOrDefault(first)}");
                }
            }
            int edges = snapshot.Blocks.Sum(b => b.Terminator.Exits.Length);
            rows.WriteLine($"{entry:x}\t{reasons.FirstOrDefault() ?? "通过"}\t{covered.Count}\t{edges}");
        }
    }
}
