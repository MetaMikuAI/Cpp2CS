using System.Buffers.Binary;
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
/// 核对工具里的事实来源。运行时函数按符号或已准入的参照命名；托管方法的入口取自代码登记表；
/// 模型给出实体、签名和布局。映像给出元数据槽、链接常量及数据区。
/// </summary>
internal sealed class BridgeFacts : IGenericEntryFacts
{
    private readonly Il2CppInput input;
    private readonly ModelMetadata metadata;
    private readonly ModelNativeFacts native;
    private readonly Dictionary<ulong, Callee> managedCallees = [];
    private readonly IReadOnlyDictionary<ulong, RuntimeName> names;
    private readonly Dictionary<ulong, Callee?> wrappers = [];
    private readonly Dictionary<ulong, string> wrapperFailures = [];
    private readonly Arm64Target target;
    private readonly RegisteredEntries entries;
    private readonly FingerprintImage image;
    private readonly Lazy<TypeInfoNames> typeInfo;
    public string Admission { get; }
    private readonly Dictionary<ulong, EntityRef?> slots = [];
    private readonly Dictionary<ulong, ElfRela> relocations = [];
    private readonly byte[] file;

    public BridgeFacts(Il2CppInput input, ModelMetadata metadata, string? symbolFile, byte[] file,
        Arm64Target target, string? fingerprint)
    {
        this.input = input;
        this.metadata = metadata;
        this.file = file;
        this.target = target;
        foreach (var relocation in input.Elf.Relocations) relocations[relocation.Address] = relocation;
        native = new(metadata, input.Code);
        entries = new(input);
        image = new(input.Elf, file, target.Unwind);
        var symbolImage = NamingCheck.OpenSymbols(input.Elf, symbolFile);
        typeInfo = new(() => new(input.Elf, file, symbolImage));
        var symbols = NamingCheck.Symbols(input, symbolImage, image: fingerprint != null ? image : null);
        var imports = image.ImportStubs();
        Dictionary<ulong, RuntimeName> known;
        if (fingerprint == null)
        {
            known = [];
            foreach (var (a, aliases) in symbols)
                if (aliases.Length == 1 || RuntimeFingerprint.RegisteredOperation(aliases) != null)
                    known.Add(a, new([.. aliases], "符号"));
            Admission = "未指定参照表";
        }
        else
        {
            var naming = NamingCheck.Match(input, image, target.Unwind, entries, symbols, RuntimeFingerprint.Read(fingerprint), imports);
            known = naming.Names.ToDictionary();
            Admission = naming.Admission;
        }
        NamingCheck.NameImports(known, imports);
        names = known;
    }

    public RuntimeLayout Layout => RuntimeLayout.Unity2022Lp64;
    public string? TypeInfoName(ulong address) => typeInfo.Value.Read(address);
    public RuntimeTypeCondition? TypeTestCondition(EntityRef type) => metadata.TypeTestCondition(type);

    public string Symbol(ulong address) => names.TryGetValue(address, out var name) ? name.Name : $"0x{address:x}";

    public Callee Callee(ulong address)
    {
        if (managedCallees.TryGetValue(address, out var known)) return known;
        string name = Symbol(address);
        ulong rva = address - input.Elf.ImageBase;
        if (native.IsEntry(rva))
        {
            var signatures = native.Signatures(rva, out string reason);
            return managedCallees[address] = new(CalleeKind.Managed, null, reason.Length == 0 ? name : $"{name}（{reason}）", "代码登记表")
            {
                Signature = signatures.Length == 1 ? signatures[0] : null,
                SharedSignatures = native.RequiresMethodArgument(rva) ? signatures : null,
            };
        }
        var direct = Direct(address);
        if (direct.Kind == CalleeKind.Runtime || names.Count == 0 || entries.Managed.Contains(address)) return direct;
        if (Wrapper(address) is { } expanded) return expanded;
        return wrapperFailures.TryGetValue(address, out var failure) ? direct with { Name = $"{direct.Name}（{failure}）" } : direct;
    }

    private Callee Direct(ulong address)
    {
        if (entries.Managed.Contains(address) || !names.TryGetValue(address, out var n)) return new(CalleeKind.Unknown, null, Symbol(address), "");
        var operation = n.Operation;
        return new(operation == null ? CalleeKind.Unknown : CalleeKind.Runtime, operation, n.Name,
            n.Depth == 0 ? n.Basis : $"{n.Basis} {n.Depth} 层，经 0x{n.Parent:x}+{n.Offset}{n.ReferencePath}");
    }

    private Callee? Wrapper(ulong address)
    {
        if (wrappers.TryGetValue(address, out var known)) return known;
        Callee? result = null;
        if (target.Unwind.Find(address) is { } f && f.Start == address && image.MayCallNamed(f, names))
        {
            ulong? expanded = WrapperTarget(target, address, Direct, out string? failure);
            if (failure != null) wrapperFailures[address] = failure;
            if (expanded is ulong to)
            {
                var callee = Direct(to);
                result = callee with { Basis = $"包装经 0x{to:x} {callee.Name}（{callee.Basis}）" };
            }
        }
        return wrappers[address] = result;
    }

    internal static ulong? WrapperTarget(Arm64Target target, ulong address, Func<ulong, Callee> direct, out string? reason)
    {
        LiftResult lift;
        try { lift = target.Lift(address); }
        catch (FlowException failure) { lift = new(null, failure.Violations[0]); }
        reason = lift.Snapshot == null ? $"包装快照不可用：{lift.Reason}" : null;
        return lift.Snapshot == null ? null : CoExecution.WrapperTarget(lift.Snapshot, direct, Abi.CallArgumentSlots);
    }

    public Dictionary<string, long> CountCalls()
    {
        var counts = new Dictionary<string, long> { ["符号"] = 0, ["导入重定位"] = 0, ["锚点"] = 0, ["同体"] = 0, ["传递"] = 0, ["包装"] = 0, ["未命名"] = 0 };
        foreach (var (address, weight) in image.CallsFrom(target.Entries.ToHashSet()))
        {
            string basis = entries.Managed.Contains(address) ? "未命名" :
                names.TryGetValue(address, out var n) ? n.Basis : Wrapper(address) != null ? "包装" : "未命名";
            counts[basis] += weight;
        }
        return counts;
    }

    private string offsetReason = "";
    public void BeginCheck() => offsetReason = "";
    public ulong? Entry(EntityRef method) => native.Entry(method);
    public GenericEntry? GenericEntry(EntityRef method) => native.GenericEntry(method);
    public EntityRef? MethodClass(EntityRef method) => native.MethodClass(method);
    public (EntityRef Entity, RgctxKind Kind)? RgctxEntry(EntityRef owner, int index) => native.RgctxEntry(owner, index);
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

    public static int Run(string casesPath, string assemblies, string binary, string metadataPath, string? symbolFile, string target, string show, string? fingerprint)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(casesPath));
        var input = Il2CppInput.Load(binary, metadataPath);
        byte[] bytes = File.ReadAllBytes(binary);
        using var metadata = ModelInput.Open(assemblies, input, bytes);
        var lifter = new Arm64Target(input.Elf, bytes,
            input.Code.Methods.Concat(input.Code.MethodInstances).Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        var facts = new BridgeFacts(input, metadata.Facts, symbolFile, bytes, lifter, fingerprint);
        if (fingerprint != null) Console.WriteLine(facts.Admission);
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
        var mutations = new List<(string Name, bool Refuted, string Detail)>();
        int indistinguishable = 0;
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
            if (result.Verdict == Verdict.Proved)
                foreach (var (offset, change, changed) in FrameMutations(body, expansion))
                {
                    var module = bodies[^1].Module;
                    var graph = IlExpander.Expand(changed, metadata.Facts, metadata.Tokens(module, body.Method.Entity), snapshot.Terms, 2, 64);
                    // 只有原始 IL 与变异 IL 在观察点确有不同，才要求现场也能区分。死写入与等价的局部重命名不能作反例。
                    var control = CoExecution.Equivalent(expansion.Graph, graph.Graph, body, facts);
                    if (!DifferentObservation(control)) { indistinguishable++; continue; }
                    var check = CoExecution.Check(snapshot, graph.Graph, changed, facts, Snapshot, output: true);
                    mutations.Add(($"{name} 0x{address:x} IL_{offset:x4} {change}", DifferentObservation(check), check.Detail));
                }
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
        Console.WriteLine($"  地址变异：IL 对照有差异 {mutations.Count} 个，原生核对被反驳 {mutations.Count(m => m.Refuted)} 个；IL 对照未取得差异 {indistinguishable} 个");
        foreach (var mutation in mutations)
            Console.WriteLine($"    {mutation.Name}：{(mutation.Refuted ? "反驳" : "未取得反驳")} {mutation.Detail}");
        foreach (var group in outcomes.GroupBy(o => o.Class).OrderBy(g => g.Key, StringComparer.Ordinal))
        {
            Console.WriteLine($"{group.Key}（{group.Count()}）");
            foreach (var outcome in group)
                Console.WriteLine($"  {outcome.Category,-12} {outcome.Name[(outcome.Name.IndexOf("::", StringComparison.Ordinal) + 2)..],-22} {outcome.Detail}");
        }
        return mutations.All(m => m.Refuted) ? 0 : 1;
    }

    private static bool DifferentObservation(ProofResult result) => result.Verdict == Verdict.Insufficient
        && new[] { "现场写了 ", "模板写了 ", "写入 ", "返回值不同", "已暴露帧对象的内容不同" }
            .Any(prefix => result.Detail.StartsWith(prefix, StringComparison.Ordinal));

    /// <summary>在已经通过正向核对的原始 IL 上改一处，保持求值栈平衡与转移目标。来源是语料中的经地址写字段与传出局部地址。</summary>
    private static IEnumerable<(int Offset, string Change, MethodBody Body)> FrameMutations(MethodBody body, Expansion expansion)
    {
        var instructions = IlDecoder.Decode(body.Code.AsSpan());
        foreach (var instruction in instructions)
        {
            if (expansion.Entries.Contains((instruction.Offset, "stfld.address")))
            {
                var code = body.Code.ToArray();
                // stfld 消耗地址和值。两个 pop 消耗同一对操作数，其余字节填 nop。
                Array.Clear(code, instruction.Offset, instruction.Size);
                code[instruction.Offset] = code[instruction.Offset + 1] = 0x26;
                yield return (instruction.Offset, "去掉经地址的写入", body with { Code = [.. code] });
            }
        }
        for (int i = 0; i + 1 < instructions.Length; i++)
        {
            var load = instructions[i];
            if (load.Opcode.Canonical != "ldloca" || instructions[i + 1].Opcode.Canonical is not ("call" or "callvirt")) continue;
            var local = (int)load.Operand;
            if (!instructions.Any(op => op.Opcode.Canonical == "ldloc" && op.Operand == local)) continue;
            // 换成同类型的新局部，保留原局部的初始化与之后的读取。
            int other = body.Locals.Length;
            bool shortForm = load.Opcode.Operand == Cpp2CS.Spec.IL.OperandKind.Variable8;
            if (other > (shortForm ? byte.MaxValue : ushort.MaxValue)) continue;
            var code = body.Code.ToArray();
            if (shortForm) code[load.Next - 1] = (byte)other;
            else BinaryPrimitives.WriteUInt16LittleEndian(code.AsSpan(load.Next - 2), (ushort)other);
            yield return (load.Offset, "给调用另一个局部的地址", body with { Locals = body.Locals.Add(body.Locals[local]), Code = [.. code] });
        }
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
            if (terminator.Kind == TerminatorKind.Invoke)
            {
                string Name(ulong address) => address == 0 ? "全捕获" : facts.TypeInfoName(address) ?? $"0x{address:x}";
                var clauses = terminator.Clauses.Select(c => $"{c.Selector}={Name(c.TypeInfo)}");
                Console.WriteLine($"    Invoke 0x{terminator.Address:x}，子句 [{string.Join(", ", clauses)}]，清理 {terminator.Cleanup}");
            }
            if (terminator.Condition is not null) Console.WriteLine($"    {terminator.Kind} {terminator.Condition}");
            for (int e = 0; e < terminator.Exits.Length; e++)
            {
                var exit = terminator.Exits[e];
                Console.WriteLine($"    → {exit.Kind} {(exit.Kind == ExitKind.Target ? exit.Target.ToString() : "")} {string.Join("; ", exit.Arguments)}");
            }
        }
    }
}
