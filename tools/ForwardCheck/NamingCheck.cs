using System.Security.Cryptography;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

internal static class NamingCheck
{
    internal static Dictionary<ulong, string[]> Symbols(Il2CppInput input, string? path, bool truthOnly = false)
    {
        IEnumerable<ElfSymbol> rows = input.Elf.DynamicSymbols;
        if (path != null)
        {
            var symbols = Elf64.Load(path);
            if (symbols.BuildId() != input.Elf.BuildId() || symbols.Machine != input.Elf.Machine)
                throw new InvalidDataException("分离符号与映像的构建标识或目标不一致");
            if (!symbols.Sections.Any(s => s.Type == 2)) throw new InvalidDataException("符号文件缺少完整符号表");
            rows = truthOnly ? symbols.FunctionSymbols() : rows.Concat(symbols.FunctionSymbols());
        }
        return rows.Where(s => s.Section != 0 && (s.Info & 15) == 2 && s.Name.Length > 0)
            .GroupBy(s => s.Value).ToDictionary(g => g.Key, g => g.Select(s => s.Name).Distinct().Order(StringComparer.Ordinal).ToArray());
    }

    internal static RuntimeNaming Match(Il2CppInput input, FingerprintImage image, UnwindIndex unwind,
        RegisteredEntries entries, Dictionary<ulong, string[]> symbols, RuntimeFingerprint table)
    {
        var anchors = symbols.Where(p => !entries.Managed.Contains(p.Key)).ToDictionary();
        if (table.Target != image.Target)
            return new(table, [], anchors, entries.Runtime, entries.Managed, image.Target);
        var sizes = table.Rows.Where(r => r.Body.Comparable).Select(r => r.Body.Length).ToHashSet();
        var bodies = new List<RuntimeBody>();
        foreach (var f in unwind.Frames)
        {
            if (entries.Managed.Contains(f.Start) || !sizes.Contains(checked((int)(f.End - f.Start)))) continue;
            var b = image.Read(f);
            if (b.Body.Comparable) bodies.Add(new(f.Start, b.Body, b.Edges.Select(e => new RuntimeEdge(e.Offset, e.Target)).ToArray()));
        }
        return new(table, bodies.ToArray(), anchors, entries.Runtime, entries.Managed, image.Target);
    }

    internal static int Run(string command, Dictionary<string, string> options)
    {
        if (!options.TryGetValue("--binary", out string? binary) || !options.TryGetValue("--metadata", out string? metadata) ||
            !options.TryGetValue("--fingerprint", out string? path)) return 2;
        var input = Il2CppInput.Load(binary, metadata);
        if (input.Elf.Machine != 183) throw new InvalidDataException("参照指纹需要 AArch64 ELF");
        var bytes = File.ReadAllBytes(binary);
        var unwind = new UnwindIndex(input.Elf, bytes);
        var image = new FingerprintImage(input.Elf, bytes, unwind);
        var entries = new RegisteredEntries(input);
        if (command == "fingerprint")
        {
            if (!options.TryGetValue("--symbols", out string? symbols) || !options.TryGetValue("--runtime-version", out string? version) ||
                !options.TryGetValue("--toolchain", out string? toolchain)) return 2;
            if (image.Target != FingerprintImage.AndroidArm64) throw new InvalidDataException("缺少 Android AArch64 目标依据");
            var names = Symbols(input, symbols);
            var imports = image.ImportStubs();
            FingerprintEdge Edge(CodeEdge edge)
            {
                var aliases = names.GetValueOrDefault(edge.Target);
                if (aliases == null) return new(edge.Offset, imports.GetValueOrDefault(edge.Target));
                string? name = entries.Managed.Contains(edge.Target) ? null : RuntimeNaming.NameOf(aliases);
                return new(edge.Offset, name) { ExcludedNames = name == null ? aliases : null };
            }
            var empty = new FingerprintBody(0, Convert.ToHexString(SHA256.HashData([])), [], false);
            var rows = new List<FingerprintRow>();
            var seen = new HashSet<ulong>();
            foreach (var f in unwind.Frames)
            {
                if (entries.Managed.Contains(f.Start)) continue;
                seen.Add(f.Start);
                var body = image.Read(f);
                var edges = body.Edges.Select(Edge).ToArray();
                rows.Add(new(names.GetValueOrDefault(f.Start) ?? [], body.Body, edges, entries.Runtime.Contains(f.Start)));
            }
            foreach (var (address, aliases) in names.Where(p => !entries.Managed.Contains(p.Key) && !seen.Contains(p.Key)))
                rows.Add(new(aliases, empty, [], entries.Runtime.Contains(address)));
            using var stream = File.OpenRead(symbols);
            new RuntimeFingerprint(1, input.Elf.BuildId(), Convert.ToHexString(SHA256.HashData(stream)), image.Target,
                version, toolchain, rows.ToArray()).Write(path);
            Console.WriteLine($"构建 {input.Elf.BuildId()}，行 {rows.Count}，可比较 {rows.Count(r => r.Body.Comparable)}");
            return 0;
        }
        if (options.ContainsKey("--symbols")) return 2;
        var table = RuntimeFingerprint.Read(path);
        var result = Match(input, image, unwind, entries, Symbols(input, null), table);
        Console.WriteLine(result.Admission);
        if (!options.TryGetValue("--truth-symbols", out string? truthPath))
        {
            foreach (var group in result.Names.Values.GroupBy(n => n.Basis)) Console.WriteLine($"{group.Key} {group.Count()}");
            return result.Admitted ? 0 : 1;
        }
        // 命名结束后才打开真值。按地址逐一对照，并核对多名是否已登记为同一操作。
        var truth = Symbols(input, truthPath, truthOnly: true).Where(p => !entries.Managed.Contains(p.Key)).ToDictionary();
        int wrong = 0;
        foreach (var basis in new[] { "符号", "同体", "传递" })
        {
            int count = 0, correct = 0;
            foreach (var (a, name) in result.Names.Where(p => p.Value.Basis == basis))
            {
                count++;
                if (truth.TryGetValue(a, out var aliases) && name.Symbols.All(aliases.Contains) &&
                    (basis == "符号" && name.Symbols.Length == 1 || RuntimeNaming.NameOf(aliases) != null)) correct++;
                else Console.WriteLine($"错误 0x{a:x} {name.Name} 对照 {string.Join('/', aliases ?? [])}");
            }
            Console.WriteLine($"{basis} 认出 {count}，正确 {correct}，错误 {count - correct}，召回 {correct}/{truth.Count}");
            wrong += count - correct;
        }
        Console.WriteLine($"合计认出 {result.Names.Count}，正确 {result.Names.Count - wrong}，错误 {wrong}，真值地址 {truth.Count}");
        return wrong == 0 ? 0 : 1;
    }
}
