using System.Buffers.Binary;
using System.Security.Cryptography;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Engine;
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

    // STT_FUNC 的非零 st_size 给出函数大小；同址别名或展开范围相互矛盾时保留不可比。
    private static Dictionary<ulong, Frame> Bounds(UnwindIndex unwind, IEnumerable<ElfSymbol> symbols)
    {
        var bounds = new Dictionary<ulong, Frame>();
        foreach (var f in unwind.Frames) bounds.Add(f.Start, f);
        foreach (var group in symbols.Where(s => s.Section != 0 && (s.Info & 15) == 2 && s.Size > 0).GroupBy(s => s.Value))
        {
            var sizes = group.Select(s => s.Size).Distinct().ToArray();
            ulong a = group.Key;
            bool hasFrame = bounds.TryGetValue(a, out var f);
            if (sizes.Length != 1 || hasFrame && f.End - a != sizes[0]) bounds.Remove(a);
            else if (!hasFrame) bounds.Add(a, new(a, checked(a + sizes[0]), 0));
        }
        return bounds;
    }

    private static HashSet<ulong> Entries(UnwindIndex unwind, RegisteredEntries entries, IEnumerable<ulong> symbols)
    {
        var result = entries.Managed.Concat(entries.Runtime).Concat(symbols).ToHashSet();
        foreach (var frame in unwind.Frames) result.Add(frame.Start);
        return result;
    }

    internal static RuntimeNaming Match(Il2CppInput input, FingerprintImage image, UnwindIndex unwind,
        RegisteredEntries entries, Dictionary<ulong, string[]> symbols, RuntimeFingerprint table)
    {
        var anchors = symbols.ToDictionary();
        foreach (var (a, name) in image.ImportStubs()) anchors[a] = [name];
        var bodies = new Dictionary<ulong, FingerprintBody>();
        if (table.Target == image.Target)
        {
            var starts = Entries(unwind, entries, anchors.Keys);
            foreach (var f in Bounds(unwind, input.Elf.DynamicSymbols).Values)
                // 代码登记中的调用器、逆向包装、封送和模块初始化入口属于生成代码。
                if (!entries.Managed.Contains(f.Start) && !entries.Runtime.Contains(f.Start)) bodies.Add(f.Start, image.Read(f, starts));
        }
        return new(table, bodies, anchors, entries.Managed, image.Target);
    }

    private static RuntimeFingerprint Generate(Il2CppInput input, FingerprintImage image, UnwindIndex unwind, RegisteredEntries entries,
        string symbols, string debug, string version, string toolchain)
    {
        if (image.Target != FingerprintImage.AndroidArm64) throw new InvalidDataException("缺少 Android AArch64 目标依据");
        string build = input.Elf.BuildId();
        if (Elf64.Load(debug).BuildId() != build) throw new InvalidDataException("调试信息与映像的构建标识不一致");
        var units = new CompilationUnits(debug);
        var names = Symbols(input, symbols);
        var bounds = Bounds(unwind, Elf64.Load(symbols).FunctionSymbols().Concat(input.Elf.DynamicSymbols));
        var imports = image.ImportStubs();
        var starts = Entries(unwind, entries, names.Keys.Concat(imports.Keys));
        var functions = starts.Where(a => !entries.Managed.Contains(a) && units.At(a) == CompilationUnits.Owner.Runtime).Order().ToArray();
        var included = functions.Concat(imports.Keys).ToHashSet();
        var empty = new FingerprintBody(0, Convert.ToHexString(SHA256.HashData([])), [], false);
        var rows = new List<FingerprintRow>();
        foreach (ulong a in starts.Except(imports.Keys).Order())
        {
            bool runtime = included.Contains(a);
            // 表外入口的 FDE 自身就是歧义证据，即使另有符号给出不同长度。
            var frame = !runtime && unwind.Find(a) is { } fde && fde.Start == a ? fde : bounds.GetValueOrDefault(a);
            var body = frame.End > a ? image.Read(frame, starts) : empty;
            bool comparable = body.Comparable;
            var references = new List<FingerprintReference>();
            foreach (var r in body.References)
            {
                if (r.Kind != ReferenceKind.Code || included.Contains(r.Target)) references.Add(r);
                else if (entries.Managed.Contains(r.Target) || units.At(r.Target) == CompilationUnits.Owner.Generated)
                    references.Add(r with { Kind = ReferenceKind.Outside, Target = 0 });
                else if (starts.Contains(r.Target))
                {
                    // 入口已知而编译单元未知。只保留引用位置与目标，不把它当作生成代码或运行时行。
                    references.Add(r);
                }
                else comparable = false;
            }
            rows.Add(new(a, runtime ? names.GetValueOrDefault(a) ?? [] : [],
                body with { References = [.. references], Comparable = comparable }, 0, runtime));
        }
        static string Hash(string path)
        {
            using var stream = File.OpenRead(path);
            return Convert.ToHexString(SHA256.HashData(stream));
        }
        ImportAnchor[] stubs = [.. imports.Select(i => new ImportAnchor(i.Key, i.Value))];
        return new(3, build, Hash(symbols), Hash(debug), image.Target, version, toolchain,
            RuntimeFingerprint.Partition([.. rows], stubs), stubs);
    }

    // LLD 的 AArch64 PLT 头占 32 字节，随后每个 JUMP_SLOT 对应 16 字节。
    // 在独立调试映像上按重定位次序定位，再核对桩实际读取的槽。
    private static IEnumerable<(ulong Address, string Name)> TruthImports(Il2CppInput input, string symbols, string? debug)
    {
        string path = symbols;
        var elf = Elf64.Load(path);
        if (!elf.Sections.Any(s => s.Name == ".plt" && s.Type == 1))
        {
            path = debug ?? Path.Combine(Path.GetDirectoryName(Path.GetFullPath(symbols))!, "libil2cpp.dbg.so");
            if (!File.Exists(path)) yield break;
            elf = Elf64.Load(path);
        }
        if (elf.BuildId() != input.Elf.BuildId() || elf.Machine != input.Elf.Machine)
            throw new InvalidDataException("导入桩的对照映像不匹配");
        var slots = elf.Relocations.Where(r => r.Type == 1026).ToArray();
        var plt = elf.Sections.SingleOrDefault(s => s.Name == ".plt" && s.Type == 1);
        if (plt == null || plt.Size != 32ul + (ulong)slots.Length * 16) yield break;
        var code = new byte[checked((int)plt.Size)];
        using var stream = File.OpenRead(path);
        stream.Position = checked((long)plt.Offset);
        stream.ReadExactly(code);
        for (int i = 0; i < slots.Length; i++)
        {
            ulong pc = plt.Address + 32 + (ulong)i * 16;
            int offset = 32 + i * 16;
            var page = Decoder.Decode(BinaryPrimitives.ReadUInt32LittleEndian(code.AsSpan(offset)));
            var load = Decoder.Decode(BinaryPrimitives.ReadUInt32LittleEndian(code.AsSpan(offset + 4)));
            var r = slots[i];
            if (page.Name != "adrp" || load.Name != "ldr" || load.Size != 64 || page.D != load.N ||
                (page.Destination(pc) & ~4095ul) + (ulong)load.Imm != r.Address || r.Addend != 0 ||
                r.Symbol >= elf.DynamicSymbols.Count) throw new InvalidDataException("对照桩与重定位不一致");
            yield return (pc, elf.DynamicSymbols[(int)r.Symbol].Name + "@plt");
        }
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
            string debug = options.GetValueOrDefault("--debug") ?? Path.Combine(Path.GetDirectoryName(binary)!, "libil2cpp.dbg.so");
            var generated = Generate(input, image, unwind, entries, symbols, debug, version, toolchain);
            generated.Write(path);
            var runtime = generated.Rows.Where(r => r.Runtime).ToArray();
            Console.WriteLine($"构建 {generated.BuildId}，运行时行 {runtime.Length}，类 {runtime.DistinctBy(r => r.Class).Count()}，可比较 {runtime.Count(r => r.Body.Comparable)}，导入 {generated.Imports.Length}，表外行 {generated.Rows.Length - runtime.Length}");
            return 0;
        }
        if (options.ContainsKey("--symbols")) return 2;
        var table = RuntimeFingerprint.Read(path);
        var result = Match(input, image, unwind, entries, Symbols(input, null), table);
        Console.WriteLine(result.Admission);
        foreach (var example in result.Counterexamples) Console.WriteLine(example);
        if (!options.TryGetValue("--truth-symbols", out string? truthPath))
        {
            foreach (var group in result.Names.Values.GroupBy(n => n.Basis)) Console.WriteLine($"{group.Key} {group.Count()}");
            return result.Admitted ? 0 : 1;
        }
        var target = new Arm64Target(input.Elf, bytes, entries.Managed.Select(a => a - input.Elf.ImageBase));
        Callee Direct(ulong a) => result.Names.TryGetValue(a, out var n) ?
            new(n.Operation == null ? CalleeKind.Unknown : CalleeKind.Runtime, n.Operation, n.Name, n.Basis) :
            new(CalleeKind.Unknown, null, "", "");
        var wrappers = new Dictionary<ulong, ulong>();
        foreach (var f in unwind.Frames)
            if (!entries.Managed.Contains(f.Start) && !entries.Runtime.Contains(f.Start) && !result.Names.ContainsKey(f.Start) && image.MayCallNamed(f, result.Names) &&
                BridgeFacts.WrapperTarget(target, f.Start, Direct, out _) is ulong to) wrappers.Add(f.Start, to);
        // 盲测完成后才读独立符号。同址真值的每个名字都应落入该参照类的名字集合。
        var truth = Symbols(input, truthPath, truthOnly: true).Where(p => !entries.Managed.Contains(p.Key)).ToDictionary();
        foreach (var (a, name) in TruthImports(input, truthPath, options.GetValueOrDefault("--truth-debug"))) truth[a] = [name];
        bool Verified(ulong a, RuntimeName n) => truth.TryGetValue(a, out var aliases) &&
            (n.Strength == null ? n.Symbols.All(aliases.Contains) : aliases.All(n.Symbols.Contains));
        int wrong = 0;
        foreach (var group in result.Names.GroupBy(p => (p.Value.Basis, p.Value.Depth)).OrderBy(g => g.Key))
        {
            int count = 0, correct = 0;
            foreach (var (a, name) in group)
            {
                count++;
                if (Verified(a, name)) correct++;
                else Console.WriteLine($"错误 0x{a:x} 类名 {string.Join('/', name.Symbols)} 对照 {string.Join('/', truth.GetValueOrDefault(a) ?? [])}");
            }
            Console.WriteLine($"{group.Key.Basis} {group.Key.Depth} 层 认出 {count}，正确 {correct}，错误 {count - correct}，召回 {correct}/{truth.Count}");
            wrong += count - correct;
        }
        Console.WriteLine($"合计认出 {result.Names.Count}，正确 {result.Names.Count - wrong}，错误 {wrong}，真值地址 {truth.Count}");
        int correctWrappers = wrappers.Count(p => Verified(p.Value, result.Names[p.Value]));
        Console.WriteLine($"另有包装 {wrappers.Count}，目标核对正确 {correctWrappers}，错误 {wrappers.Count - correctWrappers}");
        return wrong == 0 && correctWrappers == wrappers.Count && result.Admitted ? 0 : 1;
    }
}
