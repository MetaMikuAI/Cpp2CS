using System.Buffers.Binary;
using System.Text;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Facts;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Model;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 核对工具里的事实来源，只供正向核对使用。运行时函数按符号表命名；托管方法的入口取自代码登记表；
/// 模型给出实体、签名和布局。映像给出元数据槽、链接常量及数据区。
/// </summary>
internal sealed class BridgeFacts : IGenericEntryFacts
{
    private readonly Il2CppInput input;
    private readonly ModelMetadata metadata;
    private readonly ModelNativeFacts native;
    private readonly Dictionary<ulong, string> symbols = [];
    private readonly Dictionary<ulong, Callee> managedCallees = [];
    private readonly Dictionary<ulong, EntityRef?> slots = [];
    private readonly Dictionary<ulong, ElfRela> relocations = [];
    private readonly byte[] file;

    public BridgeFacts(Il2CppInput input, ModelMetadata metadata, string symbolFile, byte[] file)
    {
        this.input = input;
        this.metadata = metadata;
        this.file = file;
        foreach (var relocation in input.Elf.Relocations) relocations[relocation.Address] = relocation;
        native = new(metadata, input.Code);
        ReadSymbols(symbolFile);
    }

    /// <summary>读符号表（.symtab）：函数符号的地址到名字。</summary>
    private void ReadSymbols(string path)
    {
        byte[] file = File.ReadAllBytes(path);
        var elf = Elf64.Load(path);
        foreach (var section in elf.Sections)
        {
            if (section.Name != ".symtab") continue;
            var strings = elf.Sections[(int)section.Link];
            for (ulong at = section.Offset; at + 24 <= section.Offset + section.Size; at += 24)
            {
                var entry = file.AsSpan((int)at, 24);
                if ((entry[4] & 0xf) != 2) continue;
                ulong value = BinaryPrimitives.ReadUInt64LittleEndian(entry[8..]);
                int name = (int)(strings.Offset + BinaryPrimitives.ReadUInt32LittleEndian(entry));
                int end = Array.IndexOf(file, (byte)0, name);
                symbols.TryAdd(value, Encoding.UTF8.GetString(file, name, end - name));
            }
        }
    }

    public RuntimeLayout Layout => RuntimeLayout.Unity2022Lp64;

    public string Symbol(ulong address) => symbols.GetValueOrDefault(address, $"0x{address:x}");

    public Callee Callee(ulong address)
    {
        if (managedCallees.TryGetValue(address, out var known)) return known;
        string name = Symbol(address);
        if (native.IsEntry(address))
        {
            var signatures = native.Signatures(address, out string reason);
            return managedCallees[address] = new(CalleeKind.Managed, null, reason.Length == 0 ? name : $"{name}（{reason}）", "代码登记表")
            {
                Signature = signatures.Length == 1 ? signatures[0] : null,
                SharedSignatures = native.RequiresMethodArgument(address) ? signatures : null,
            };
        }
        if (symbols.TryGetValue(address, out var symbol) && RuntimeOperations.BySymbol(symbol) is { } operation)
            return new(CalleeKind.Runtime, operation, name, "符号表");
        return new(CalleeKind.Unknown, null, name, "");
    }

    private string offsetReason = "";
    public void BeginCheck() => offsetReason = "";
    public ulong? Entry(EntityRef method) => native.Entry(method);
    public GenericEntry? GenericEntry(EntityRef method) => native.GenericEntry(method);
    public int? InstanceFieldOffset(EntityRef field) => native.Offset(field, FieldStorage.Instance, out offsetReason);
    public int? StaticFieldOffset(EntityRef field) => native.Offset(field, FieldStorage.Static, out offsetReason);

    public string Detail(ProofResult result) => result.Verdict == Verdict.MissingFact && offsetReason.Length != 0 ? offsetReason : result.Detail;

    /// <summary>
    /// 元数据槽的初始编码（Il2CppMetadataUsage）：最低位为 1，低 32 位的高 3 位是用途，中间 28 位是下标。
    /// </summary>
    private (uint Usage, int Index) SlotEncoding(ulong address)
    {
        if (input.Elf.FileOffset(address, 8) is not int offset) return default;
        ulong value = BinaryPrimitives.ReadUInt64LittleEndian(file.AsSpan(offset, 8));
        if (value > uint.MaxValue || (value & 1) == 0) return default;
        return ((uint)value >> 29, (int)((value & 0x1FFFFFFE) >> 1));
    }

    public bool MetadataSlot(ulong address) => SlotEncoding(address).Usage is >= 1 and <= 7;

    /// <summary>
    /// vm/MetadataCache.cpp 的 InitializeRuntimeMetadata 经 GlobalMetadata::InitializeRuntimeMetadata 初始化槽。
    /// 用途 1、5 分别指向运行时类型和字符串字面量；GetMethodInfoFromEncodedIndex 的
    /// kIl2CppMetadataUsageMethodDef（3）取方法定义，kIl2CppMetadataUsageMethodRef（6）取方法实例。
    /// </summary>
    public EntityRef? EntityAtSlot(ulong address)
    {
        if (slots.TryGetValue(address, out var known)) return known;
        var (usage, index) = SlotEncoding(address);
        var model = input.Model;
        return slots[address] = usage switch
        {
            1 when index < model.RuntimeTypes.Count && metadata.Keys.TypeKey(model.RuntimeTypes[index]) is long key => new(EntityKind.Type, key),
            3 when index < model.Methods.Count => new(EntityKind.Method, index),
            5 when index < model.StringLiterals.Count && metadata.Keys.StringKey(model.StringLiterals[index]) is long key => new(EntityKind.String, key),
            6 when index < model.MethodInstances.Count && metadata.Keys.MethodKey(model.MethodInstances[index]) is long key => new(EntityKind.Method, key),
            _ => null,
        };
    }

    public EntityRef? TypeAtSlot(ulong address) => EntityAtSlot(address) is { Kind: EntityKind.Type } type ? type : null;
    public EntityRef? StringAtSlot(ulong address) => EntityAtSlot(address) is { Kind: EntityKind.String } literal ? literal : null;
    public EntityRef? MethodAtSlot(ulong address) => EntityAtSlot(address) is { Kind: EntityKind.Method } method ? method : null;

    public ulong? LinkConstant(ulong address)
    {
        const uint RelativeRelocation = 1027, ReadOnlyAfterRelocation = 0x6474e552;
        bool readOnly = false;
        foreach (var segment in input.Elf.Segments)
            readOnly |= segment.Type == ReadOnlyAfterRelocation && address >= segment.Address && address + 8 <= segment.Address + segment.MemorySize;
        if (!readOnly) return null;
        if (relocations.TryGetValue(address, out var relocation))
            return relocation.Type == RelativeRelocation ? unchecked((ulong)relocation.Addend) : null;
        return input.Elf.FileOffset(address, 8) is int offset ? BinaryPrimitives.ReadUInt64LittleEndian(file.AsSpan(offset, 8)) : null;
    }

    public bool InImageData(ulong address)
    {
        foreach (var segment in input.Elf.Segments)
            if (segment.Type == 1 && (segment.Flags & 2) != 0 && address >= segment.Address && address < segment.Address + segment.MemorySize) return true;
        return false;
    }
}

/// <summary>
/// 原生一侧的正向核对（设计第 15 节）：语料方法的真实 IL 按目录展开成效果图，与原生快照共同执行。
/// 不经过发现与选择。结果分三类：通过；不通过（缺目录项、缺事实、缺独立关系的行、理论不够、预算）；不适用（没有快照）。
/// </summary>
internal static class NativeCheck
{
    private sealed record Outcome(string Category, string Name, string Class, string Detail);

    public static int Run(string casesPath, string assemblies, string binary, string metadataPath, string symbolFile, string target, string show)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(casesPath));
        var input = Il2CppInput.Load(binary, metadataPath);
        byte[] bytes = File.ReadAllBytes(binary);
        using var metadata = ModelInput.Open(assemblies, input, bytes);
        var facts = new BridgeFacts(input, metadata.Facts, symbolFile, bytes);
        var lifter = new Arm64Target(input.Elf, bytes,
            input.Code.Methods.Concat(input.Code.MethodInstances).Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        // 别的方法的快照，展开调用时使用。提升不出来、或通不过快照校验的方法没有快照。
        var lifts = new Dictionary<ulong, MethodSnapshot?>();
        MethodSnapshot? Snapshot(ulong entry)
        {
            if (lifts.TryGetValue(entry, out var known)) return known;
            try
            {
                return lifts[entry] = lifter.Lift(entry).Snapshot;
            }
            catch (FlowException)
            {
                return lifts[entry] = null;
            }
        }
        var outcomes = new List<Outcome>();
        var proved = new List<(string Name, ulong Address, string Signature, string Il)>();
        var bodies = new List<(string Name, string Signature, string Il, Module Module, MethodBody Body)>();
        var assumed = new SortedDictionary<string, int>(StringComparer.Ordinal);
        long steps = 0, paths = 0;

        foreach (var item in document.RootElement.EnumerateArray())
        {
            var description = item.GetProperty("case");
            var method = item.GetProperty("method");
            string category = description.GetProperty("category").GetString()!;
            string name = $"{description.GetProperty("type").GetString()}::{description.GetProperty("method").GetString()}";
            bool shown = show.Length > 0 && name.EndsWith("::" + show, StringComparison.Ordinal);
            void Add(string @class, string detail) => outcomes.Add(new(category, name, @class, detail));

            var targets = item.GetProperty("mapping").GetProperty("targets");
            if (!targets.TryGetProperty(target, out var places) || places.GetArrayLength() == 0) { Add("不适用", "用例清单里没有这个目标的地址"); continue; }
            ulong address = Convert.ToUInt64(places[0].GetProperty("address").GetString()!, 16);
            LiftResult lifted;
            try
            {
                lifted = lifter.Lift(address);
            }
            catch (FlowException failure)
            {
                Add("不适用", "快照校验失败：" + failure.Violations[0]);
                continue;
            }
            if (lifted.Snapshot is not { } snapshot) { Add("不适用", "没有快照：" + lifted.Reason); continue; }
            if (shown) Dump(snapshot, facts);

            MethodBody body;
            Expansion expansion;
            try
            {
                var module = metadata.Load(Path.GetFileNameWithoutExtension(method.GetProperty("assembly").GetString()!))
                    ?? throw new ExpansionException("程序集不在目录里", method.GetProperty("assembly").GetString()!);
                body = metadata.Body(module, Convert.ToInt32(method.GetProperty("token").GetString()!, 16));
                if (!Convert.ToHexString(body.Code.AsSpan()).Equals(method.GetProperty("il_hex").GetString(), StringComparison.OrdinalIgnoreCase))
                    throw new ExpansionException("IL 与语料记录不一致", "");
                expansion = IlExpander.Expand(body, metadata.Facts, metadata.Tokens(module, body.Method.Entity), snapshot.Terms, 1, 64);
            }
            catch (ExpansionException failure)
            {
                Add("缺目录项", failure.Message);
                continue;
            }

            string signature = method.GetProperty("signature_blob").GetString()!, il = method.GetProperty("il_hex").GetString()!;
            bodies.Add((name, signature, il, metadata.Load(Path.GetFileNameWithoutExtension(method.GetProperty("assembly").GetString()!))!, body));
            facts.BeginCheck();
            var result = CoExecution.Check(snapshot, expansion.Graph, body, facts, Snapshot);
            if (result.Verdict == Verdict.Proved) proved.Add((name, address, signature, il));
            steps += result.Steps;
            paths += result.Paths;
            foreach (string assumption in result.Assumptions) assumed[assumption] = assumed.GetValueOrDefault(assumption) + 1;
            Add(result.Verdict switch
            {
                Verdict.Proved => "通过",
                Verdict.MissingFact => "缺事实",
                Verdict.MissingIndependence => "缺独立关系的行",
                Verdict.Insufficient => "理论不够",
                _ => "预算",
            }, facts.Detail(result));
        }

        // 交叉对照（设计第 15 节的对抗核对）：把通过的用例的原生代码，与签名相同、IL 不同的另一个用例的真实 IL 对照，引擎必须反驳。
        int crossed = 0, refuted = 0;
        var accepted = new List<string>();
        foreach (var (name, address, signature, il) in proved)
            foreach (var other in bodies)
            {
                if (other.Signature != signature || other.Il == il) continue;
                var snapshot = lifter.Lift(address).Snapshot!;
                var expansion = IlExpander.Expand(other.Body, metadata.Facts, metadata.Tokens(other.Module, other.Body.Method.Entity), snapshot.Terms, 1, 64);
                crossed++;
                if (CoExecution.Check(snapshot, expansion.Graph, other.Body, facts, Snapshot).Verdict == Verdict.Proved) accepted.Add($"{name} 的原生代码 ≡ {other.Name} 的 IL");
                else refuted++;
            }

        int Count(string @class) => outcomes.Count(o => o.Class == @class);
        int failed = outcomes.Count - Count("通过") - Count("不适用");
        Console.WriteLine($"原生一侧的正向核对（{target}）：用例 {outcomes.Count} 个，通过 {Count("通过")} 个，不通过 {failed} 个，不适用 {Count("不适用")} 个");
        Console.WriteLine($"  不通过：缺目录项 {Count("缺目录项")}，缺事实 {Count("缺事实")}，缺独立关系的行 {Count("缺独立关系的行")}，理论不够 {Count("理论不够")}，预算 {Count("预算")}");
        Console.WriteLine($"  共同执行的路径 {paths} 条，步数 {steps}");
        foreach (var (assumption, count) in assumed) Console.WriteLine($"  用到 {assumption}：{count} 个用例");
        Console.WriteLine($"  交叉对照：{crossed} 对（通过的用例的原生代码配上签名相同的另一个用例的 IL），被反驳 {refuted} 对，被证明 {accepted.Count} 对");
        foreach (string pair in accepted) Console.WriteLine($"    被证明：{pair}");
        foreach (var group in outcomes.GroupBy(o => o.Class).OrderBy(g => g.Key, StringComparer.Ordinal))
        {
            Console.WriteLine($"{group.Key}（{group.Count()}）");
            foreach (var outcome in group)
                Console.WriteLine($"  {outcome.Category,-12} {outcome.Name[(outcome.Name.IndexOf("::", StringComparison.Ordinal) + 2)..],-22} {outcome.Detail}");
        }
        return 0;
    }

    private static void Dump(MethodSnapshot snapshot, BridgeFacts facts)
    {
        foreach (var block in snapshot.Blocks)
        {
            Console.WriteLine($"{block.Id}（参数 {block.Parameters.Length} 个）");
            for (int i = 0; i < block.Occurrences.Length; i++)
            {
                var occurrence = block.Occurrences[i];
                string text = occurrence switch
                {
                    ReadOccurrence read => $"读 {read.Width} 位 [{read.Location}]",
                    WriteOccurrence write => $"写 [{write.Location}] ← {write.Value}",
                    CallOccurrence call => $"调用{(call.ByJump ? "（跳转）" : "")} {(call.Target is { IsConstant: true } t ? facts.Symbol((ulong)t.Value) : call.Target?.ToString())}"
                        + $"（{string.Join(", ", call.ArgumentSlots.Zip(call.Arguments.ToArray(), (s, v) => $"{s}={v}"))}）",
                    _ => occurrence.Kind.ToString(),
                };
                Console.WriteLine($"    {i}: {text}");
            }
            var terminator = block.Terminator;
            if (terminator.Condition is not null) Console.WriteLine($"    {terminator.Kind} {terminator.Condition}");
            for (int e = 0; e < terminator.Exits.Length; e++)
            {
                var exit = terminator.Exits[e];
                Console.WriteLine($"    → {exit.Kind} {(exit.Kind == ExitKind.Target ? exit.Target.ToString() : "")} {string.Join("; ", exit.Arguments)}");
            }
        }
    }
}
