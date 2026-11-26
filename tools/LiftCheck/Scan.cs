using System.Globalization;
using Cpp2CS.Input;
using Cpp2CS.Target;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Tools.LiftCheck;

internal sealed class Scan
{
    readonly string prefix;
    public byte[] FileBytes { get; }
    public Elf64 Elf { get; }
    public Arm64Target Target { get; }

    public Scan(string binary, string metadata, string prefix)
    {
        this.prefix = prefix;
        FileBytes = File.ReadAllBytes(binary);
        var input = Il2CppInput.Load(binary, metadata);
        Elf = input.Elf;
        var rvas = input.Code.Methods.Concat(input.Code.MethodInstances)
            .Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value);
        Target = new(Elf, FileBytes, rvas);
    }

    public const string InvalidSnapshot = "快照校验失败";

    public LiftResult Lift(ulong entry, LiftLocations locations, TextWriter violations)
    {
        try { return Target.Lift(entry, locations); }
        catch (FlowException exception)
        {
            violations.WriteLine($"{entry:x}\t{exception.Violations[0]}");
            return new(null, InvalidSnapshot);
        }
    }

    public void Inventory(ulong from = 0, ulong until = ulong.MaxValue)
    {
        var counts = new Dictionary<uint, (int Count, bool Unknown, string? Extension)>();
        using var listing = new StreamWriter(prefix + ".functions.local.tsv");
        using var witnesses = new StreamWriter(prefix + ".candidates.local.tsv");
        using var violations = new StreamWriter(prefix + ".scan-violations.local.tsv");
        using var switches = new StreamWriter(prefix + ".switches.local.tsv");
        using var rejected = new StreamWriter(prefix + ".rejected.local.tsv");
        using var unknown = new BinaryWriter(File.Create(prefix + ".unknown.local.bin"));
        foreach (ulong entry in Target.Entries)
        {
            if (entry < from || entry >= until) continue;
            var frame = Target.Unwind.Find(entry);
            if (frame == null) { listing.WriteLine($"{entry:x}\t-\t-\t缺少 FDE"); continue; }
            var seen = new HashSet<uint>();
            HashSet<string>? extensions = null;
            for (ulong pc = frame.Value.Start; pc < frame.Value.End; pc += 4)
            {
                uint word = Target.Word(pc);
                ref var record = ref System.Runtime.InteropServices.CollectionsMarshal.GetValueRefOrAddDefault(counts, word, out bool exists);
                if (!exists)
                {
                    var insn = Decoder.Decode(word);
                    record.Unknown = insn.Form == Form.Unknown;
                    record.Extension = insn.Extension;
                }
                if (record.Extension != null) (extensions ??= []).Add(record.Extension);
                record.Count++;
                if (record.Unknown) seen.Add(word);
            }
            unknown.Write(seen.Count);
            foreach (var word in seen) unknown.Write(word);
            var locations = new LiftLocations(false);
            var result = Lift(entry, locations, violations);
            foreach (var (branch, table) in locations.Switches)
                switches.WriteLine($"{entry:x}\t{branch:x}\t{table.Arms.Length}\t{result.Reason ?? "成功"}");
            if (locations.UnresolvedBranch is { } jump)
                rejected.WriteLine($"{entry:x}\t{jump:x}\t{locations.BranchReason}");
            if (result.Snapshot != null && extensions != null)
                witnesses.WriteLine($"{entry:x}\t{frame.Value.End - frame.Value.Start}\t{string.Join(',', extensions.Order())}");
            listing.WriteLine($"{entry:x}\t{frame.Value.Start:x}\t{frame.Value.End:x}\t{result.Reason ?? "成功"}");
        }
        using var words = new StreamWriter(prefix + ".words.local.tsv");
        foreach (var (word, count) in counts.OrderBy(kv => kv.Key))
            words.WriteLine($"{word:x8}\t{count.Count}\t{AssemblyText.Format(Decoder.Decode(word), 0x100000000)}");
    }

    // 按扫描清单复核每个已确认的表，导出能直接回到 ELF 查证的地址与位宽。
    public void Layouts()
    {
        using var layout = new StreamWriter(prefix + ".layouts.local.tsv");
        var records = File.ReadLines(prefix + ".switches.local.tsv").Select(l => l.Split('\t'));
        foreach (var group in records.GroupBy(r => ulong.Parse(r[0], NumberStyles.HexNumber)))
        {
            var locations = new LiftLocations(false);
            var result = Target.Lift(group.Key, locations);
            if (locations.Switches.Count != group.Count()) throw new InvalidDataException("表数与扫描清单不符");
            foreach (var r in group)
            {
                var t = locations.Switches[ulong.Parse(r[1], NumberStyles.HexNumber)];
                if (int.Parse(r[2]) != t.Arms.Length || r[3] != (result.Reason ?? "成功"))
                    throw new InvalidDataException("表项数或提升结果与扫描清单不符");
                layout.WriteLine($"{r[0]}\t{r[1]}\t{t.Load:x}\t{t.Address:x}\t{t.Arms.Length}\tu{8 * t.Bytes}\t{t.Basis:x}");
            }
        }
    }

    public IEnumerable<ulong> Sample(int limit, int seed)
    {
        var entries = File.ReadLines(prefix + ".functions.local.tsv").Select(line => line.Split('\t'))
            .Where(row => row[3] == "成功").Select(row => ulong.Parse(row[0], NumberStyles.HexNumber)).ToArray();
        if (limit != 0)
        {
            new Random(seed).Shuffle(entries);
            Array.Resize(ref entries, Math.Min(limit, entries.Length));
        }
        return entries.Order();
    }
}
