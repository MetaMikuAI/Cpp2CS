using System.Diagnostics;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Cli;

/// <summary>
/// L3 + L4 恢复：按全程序、程序集、命名空间或方法清单选择有代码的方法定义，把无洞的方法体写成 CIL，
/// 再把含已写出方法的顶层类型反编译为 C#。输出：
/// recovery.jsonl（每个方法：地址、状态、洞，无洞时还有方法体用到的构造与语句数）、holes.txt（按原因分桶）、
/// emitted.tsv（已写出的方法：程序集、顶层类型、地址、方法、写出后的元数据标记）、assemblies/（骨架 + 已写出的方法体）、src/（C#）。
/// --methods 只恢复外部清单中的方法：每行以十六进制地址和方法名开头，二者都要与本二进制一致。
/// </summary>
internal static class RecoverCommand
{
    private static readonly JsonSerializerOptions Json = new() { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };

    public static int Run(string binary, string metadata, string output, string[] options)
    {
        string[] namespaces = [];
        var scopeCount = 0;
        var all = false;
        var noSource = false;
        string[]? assembliesFilter = null;
        var limit = int.MaxValue;
        string? list = null;
        string? accessorEvidence = null;
        string? rejectedAccessors = null;
        for (var i = 0; i < options.Length; i++)
        {
            if (options[i] == "--all") { all = true; scopeCount++; continue; }
            if (options[i] == "--no-source") { noSource = true; continue; }
            var option = options[i];
            if (++i == options.Length) throw new ArgumentException($"{option} 缺少参数");
            if (option == "--namespaces") { namespaces = options[i].Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries); scopeCount++; }
            else if (option == "--assemblies") { assembliesFilter = options[i].Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries); scopeCount++; }
            else if (option == "--limit") limit = int.Parse(options[i]);
            else if (option == "--methods") { list = options[i]; scopeCount++; }
            else if (option == "--rejected-accessors") rejectedAccessors = options[i];
            else if (option == "--verified-accessors") accessorEvidence = options[i];
            else throw new ArgumentException($"未知参数 {option}");
        }
        if (scopeCount != 1 || !(all || namespaces.Length > 0 || assembliesFilter is { Length: > 0 } || !string.IsNullOrWhiteSpace(list)))
        {
            Console.Error.WriteLine("必须且只能指定一种恢复范围：--all、--assemblies、--namespaces 或 --methods。");
            return 2;
        }
        all |= assembliesFilter is not null;
        var facts = FactsBuilder.Build(binary, metadata, Console.Error.WriteLine);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        MethodDef[] methods;
        if (list is null)
        {
            methods = facts.Model.Methods.Where(m => m.Address != 0 && (all || InNamespaces(m.Owner, namespaces))
                && (assembliesFilter is null || assembliesFilter.Contains(m.Owner.Assembly, StringComparer.Ordinal)) && facts.Code.RegionOf(m.Address) == CodeRegion.Managed)
                .Take(limit).ToArray();
            Console.Error.WriteLine($"恢复 {methods.Length} 个方法（{(all ? assembliesFilter is null ? "全程序方法定义" : string.Join(", ", assembliesFilter) : string.Join(", ", namespaces))}）");
        }
        else
        {
            var byAddress = facts.Model.Methods.Where(m => m.Address != 0).ToLookup(m => m.Address);
            methods = File.ReadLines(list).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t')).Select(f =>
            {
                var address = Convert.ToUInt64(f[0], 16);
                return byAddress[address].SingleOrDefault(m => new MethodRef(m, [], []).ToString() == f[1])
                    ?? throw new InvalidDataException($"{list}: 0x{address:x} 处没有方法 {f[1]}");
            }).ToArray();
            Console.Error.WriteLine($"恢复 {methods.Length} 个方法（{list}）");
        }

        var watch = Stopwatch.StartNew();
        // 单线程：FieldLayouts 的缓存不是线程安全的
        var recovery = new MethodRecovery(facts, types);
        var targets = methods.Select(m => recovery.Recover(new MethodRef(m, [], []), m.Address)).ToArray();
        var bytes = targets.Select(r => r.Entry).Distinct().ToDictionary(e => e,
            e => checked((long)(facts.Code.At(e) ?? throw new InvalidDataException($"0x{e:x} 没有 L0 函数边界")).Size));
        Console.Error.WriteLine($"L3 {watch.Elapsed.TotalSeconds:F1} s");

        watch.Restart();
        var skeleton = new Skeleton(facts.Model);
        var emitter = new BodyEmitter(skeleton, types);
        var emitProblems = new Dictionary<MethodRecoveryResult, string>();
        var emitted = new List<MethodRecoveryResult>();
        var closure = new AccessorRecovery(facts, types, recovery, emitter, targets, AutoPropertyManifest.ReadRejected(rejectedAccessors));
        var evidence = AccessorEvidence.Read(accessorEvidence);
        var descriptions = closure.Candidates.Values.ToDictionary(c => c.Method.Method, c => AccessorEvidence.Describe(facts, skeleton, c));
        var inlineDescriptions = closure.InlineCandidates.ToDictionary(p => p.Key, p => AccessorEvidence.Describe(facts, skeleton, p.Value.Method));
        closure.Rewrite(types, emitter, c => evidence.Contains(descriptions[c.Method.Method]), m => evidence.Contains(inlineDescriptions[m]));
        var results = closure.All.ToArray();
        var dependencies = closure.Dependencies.Select(r => r.Method.Method).ToHashSet();
        foreach (var result in closure.Dependencies) bytes[result.Entry] = result.Entry == 0 ? 0 : checked((long)facts.Code.At(result.Entry)!.Size);
        var problems = closure.Problems;
        foreach (var result in results.Where(r => r.Body is not null))
        {
            if (problems.TryGetValue(result.Body!, out var problem)) emitProblems[result] = problem;
            else emitted.Add(result);
        }
        // 部分方法体：有洞的范围方法写出已恢复的部分（洞写成 Cpp2CS.Unrecovered 标记），只供阅读，不进 emitted.tsv 与指标。
        var partials = results.Where(r => r.Body is null && r.Partial is not null && !dependencies.Contains(r.Method.Method)).ToArray();
        emitter.IgnoreAccess = true;
        var partialProblems = emitter.Emit(partials.Select(r => r.Partial!));
        emitter.IgnoreAccess = false;
        var partialEmitted = partials.Where(r => !partialProblems.ContainsKey(r.Partial!)).ToHashSet();
        Console.Error.WriteLine($"CIL {watch.Elapsed.TotalSeconds:F1} s");

        Directory.CreateDirectory(output);
        AutoPropertyManifest.Write(output, closure, rejectedAccessors);
        File.WriteAllLines(Path.Combine(output, "stack-methodinfo.tsv"),
            new[] { "entry\tsite\tstore\tsp\tslot\tmethod" }.Concat(recovery.StackCalls.OrderBy(c => c.Site)
                .Select(c => $"0x{c.Entry:x}\t0x{c.Site:x}\t0x{c.Store:x}\t{c.Sp}\t{c.Slot}\t{c.Method}")));
        using (var writer = new StreamWriter(Path.Combine(output, "recovery.jsonl")))
            foreach (var result in results)
            {
                var status = result.Body is null ? "hole" : emitProblems.ContainsKey(result) ? "emit-failed" : "emitted";
                writer.WriteLine(JsonSerializer.Serialize(new
                {
                    address = $"0x{result.Entry:x}", method = result.Method.ToString(), status, bytes = bytes[result.Entry],
                    dependency = dependencies.Contains(result.Method.Method),
                    bodySource = result.Body is null ? null : closure.Synthesized.ContainsKey(result.Method.Method) ? "language-definition" : "native-recovery",
                    accessorProof = closure.LanguageAccessors.ContainsKey(result.Method.Method) ? "language-definition" : null,
                    holes = result.Holes.Select(h => new { address = $"0x{h.Address:x}", reason = h.Reason, derived = h.Derived }),
                    emitProblem = emitProblems.GetValueOrDefault(result),
                    partial = partialEmitted.Contains(result),
                    statements = result.Body?.Blocks.Sum(b => b.Statements.Count),
                    regions = result.Body?.Regions.Count,
                    features = result.Body is { } body ? Features(body) : null,
                }, Json));
            }

        var targetResults = targets.ToHashSet();
        var report = Report(targets, emitted.Where(targetResults.Contains).ToList(), emitProblems.Where(p => targetResults.Contains(p.Key)).ToDictionary(),
            targets.Select(r => r.Entry).Distinct().ToDictionary(e => e, e => bytes[e]));
        report.AppendLine($"F9 依赖访问器：{closure.Dependencies.Count}，已写出 {emitted.Count(r => dependencies.Contains(r.Method.Method))}；不计入范围方法/字节指标");
        report.AppendLine($"F9b 语言定义候选：{closure.LanguageAccessors.Count}，合成 {closure.Synthesized.Count}（有原生代码 {closure.Synthesized.Count(p => p.Key.Address != 0)}，无原生代码 {closure.Synthesized.Count(p => p.Key.Address == 0)}）；其余保留普通恢复体");
        report.AppendLine($"F9 可用候选：{descriptions.Count}，证据匹配 {descriptions.Values.Count(evidence.Contains)}，实际认回目标 {emitter.AccessorCalls.Values.Select(a => a.Method).Distinct().Count()}");
        report.AppendLine($"内联认回候选：{inlineDescriptions.Count}，证据匹配 {inlineDescriptions.Values.Count(evidence.Contains)}，认回调用点 {emitter.InlineCalls.Count}（被调方法 {emitter.InlineCalls.Values.Distinct().Count()} 个）");
        AccessorEvidence.Write(Path.Combine(output, "accessor-evidence-input.tsv"), descriptions.Values.Concat(inlineDescriptions.Values).Where(evidence.Contains));
        File.WriteAllLines(Path.Combine(output, "accessor-candidates.tsv"), descriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "inline-candidates.tsv"), inlineDescriptions.Values.Order(StringComparer.Ordinal));
        File.WriteAllLines(Path.Combine(output, "accessor-calls.tsv"), emitted.SelectMany(r => AccessorRecovery.Fields(r.Body!)
            .Select(x => (x.Address, Accessor: x.Value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null }))
            .Where(x => x.Accessor is not null).Select(x => $"0x{r.Entry:x}\t{r.Method}\t0x{x.Address:x}\t0x{x.Accessor!.Method.Method.Address:x}\t{x.Accessor.Method}\t{(x.Accessor.Write ? "setter" : "getter")}\t{(x.Accessor.Method.Method.IsStatic ? "static" : "instance")}")));

        watch.Restart();
        var assemblies = Path.Combine(output, "assemblies");
        skeleton.Write(assemblies);
        // 第六列是方法在写出的程序集中的元数据标记（Cecil 写出时分配）；末尾追加范围/依赖标记，原有列位置不变
        var emittedRows = emitted.Select(r => (Top: Top(r.Method.Method.Owner), r.Method))
            .Select(x => $"{x.Top.Assembly}\t{x.Top.Namespace}\t{x.Top.SimpleName}\t0x{x.Method.Method.Address:x}\t{x.Method}\t0x{skeleton.Method(x.Method.Method).MetadataToken.ToUInt32():x8}\t{(dependencies.Contains(x.Method.Method) ? "dependency" : "target")}").ToArray();
        // C# 输出用的方法体（只写进反编译用的 assemblies-src，执行对照仍用 assemblies 里的原样 CIL）：
        // async 入口方法与 MoveNext 都有方法体时提升成 async/await（AsyncLifting），全部方法体再经 SourceRewriter 整理。
        var written = emitted.Concat(partialEmitted).Where(r => !dependencies.Contains(r.Method.Method)).GroupBy(r => r.Method.Method).ToDictionary(g => g.Key, g => g.First().Body ?? g.First().Partial!);
        var sourceBodies = new Dictionary<MethodDef, ManagedBody>(written);
        var liftFailures = new Dictionary<string, int>();
        var liftRows = new List<string> { "entry\tmethod\tstatus\treason" };
        var lifted = new HashSet<MethodDef>();
        foreach (var (method, kickoff) in written)
        {
            if (AsyncLifting.StateMachineOf(kickoff) is not DefinitionRef machine
                || machine.Definition.Methods.FirstOrDefault(m => m.Name == "MoveNext") is not { } moveNext || !written.TryGetValue(moveNext, out var machineBody)) continue;
            if (AsyncLifting.Lift(kickoff, machineBody, out var reason) is { } body)
            {
                sourceBodies[method] = body; lifted.Add(method);
                liftRows.Add($"0x{method.Address:x}\t{method}\tlifted\t");
                continue;
            }
            liftRows.Add($"0x{method.Address:x}\t{method}\tpreserved\t{reason}");
            if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1") Console.Error.WriteLine($"  [未提升] {method}：{reason}");
            var key = string.Join(" ", reason.Split(' ').Skip(reason.StartsWith("async", StringComparison.Ordinal) ? 2 : 0).Take(1));
            liftFailures[key] = liftFailures.GetValueOrDefault(key) + 1;
        }
        File.WriteAllLines(Path.Combine(output, "async-lifting.tsv"), liftRows);
        emitter.IgnoreAccess = true;
        var libraryCalls = new SourceLibraryCalls(facts, types, recovery);
        var rewritten = sourceBodies.ToDictionary(p => p.Key, p => libraryCalls.Rewrite(SourceRewriter.Rewrite(p.Value, types)));
        File.WriteAllLines(Path.Combine(output, "source-library-calls.tsv"), libraryCalls.Evidence);
        if (Environment.GetEnvironmentVariable("CPP2CS_SOURCE_DUMP") is { Length: > 0 } dump)
            foreach (var statement in rewritten.Values.SelectMany(b => b.Blocks).SelectMany(b => b.Statements).Where(s => s.ToString().Contains(dump, StringComparison.Ordinal)))
                Console.Error.WriteLine($"  [整理后] {statement}");
        var sourceProblems = emitter.Emit(rewritten.Values);
        if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1")
            foreach (var (method, body) in rewritten.Where(p => sourceProblems.ContainsKey(p.Value))) Console.Error.WriteLine($"  [整理后写不出] {method}：{sourceProblems[body]}");
        // 整理后写不出的退回整理前（提升过的入口方法退回提升后的方法体）。
        var fallback = rewritten.Where(p => sourceProblems.ContainsKey(p.Value)).Select(p => sourceBodies[p.Key]).ToArray();
        var liftProblems = emitter.Emit(fallback);
        emitter.IgnoreAccess = false;
        lifted.RemoveWhere(m => sourceProblems.ContainsKey(rewritten[m]) && liftProblems.ContainsKey(sourceBodies[m]));
        var sourceAssemblies = Path.Combine(output, "assemblies-src");
        skeleton.Write(sourceAssemblies);
        var sources = Path.Combine(output, "src");
        if (Directory.Exists(sources)) Directory.Delete(sources, true);
        Directory.CreateDirectory(sources);
        var invalid = Path.GetInvalidFileNameChars();
        var files = 0;
        foreach (var group in emitted.Concat(partialEmitted).Select(r => Top(r.Method.Method.Owner)).Distinct().Where(_ => !noSource).GroupBy(t => t.Assembly))
        {
            var wanted = group.Select(t => (t.Namespace, t.SimpleName)).ToHashSet();
            foreach (var source in Decompilation.Decompile(Path.Combine(sourceAssemblies, group.Key), sourceAssemblies, t => wanted.Contains((t.Namespace, t.Name)), false, recoveringBodies: true))
            {
                File.WriteAllText(Path.Combine(sources, new string((group.Key + "_" + source.TypeName).Select(c => invalid.Contains(c) ? '_' : c).ToArray()) + ".cs"), source.Source);
                files++;
            }
        }
        File.WriteAllLines(Path.Combine(output, "emitted.tsv"), emittedRows);
        report.AppendLine();
        report.AppendLine($"部分方法体：有洞的范围方法 {partials.Length} 个有部分方法体，写出 {partialEmitted.Count} / {partialEmitted.Sum(r => bytes[r.Entry])} 字节（洞写成 Cpp2CS.Unrecovered 标记；不计入指标）");
        report.AppendLine($"C# 整理：{rewritten.Count - sourceProblems.Count} / {rewritten.Count} 个方法体经 SourceRewriter 整理后写出");
        report.AppendLine($"async 提升：{lifted.Count} 个方法写成 async/await；未提升 {liftFailures.Values.Sum()}（{string.Join("；", liftFailures.OrderByDescending(p => p.Value).Take(8).Select(p => $"{p.Key} {p.Value}"))}）");
        report.AppendLine($"C#：{files} 个类型文件（只含已写出方法或部分方法体所在的顶层类型；其余成员仍为骨架占位体），{watch.Elapsed.TotalSeconds:F1} s");
        File.WriteAllText(Path.Combine(output, "holes.txt"), report.ToString());
        Console.Write(report);
        return 0;
    }

    private static StringBuilder Report(MethodRecoveryResult[] results, List<MethodRecoveryResult> emitted,
        Dictionary<MethodRecoveryResult, string> emitProblems, Dictionary<ulong, long> bytes)
    {
        long Bytes(IEnumerable<MethodRecoveryResult> rows) => rows.Select(r => r.Entry).Distinct().Sum(e => bytes[e]);
        var total = Bytes(results);
        double Fraction(long size) => (double)size / Math.Max(1, total);
        var recovered = results.Where(r => r.Body is not null).ToArray();
        var report = new StringBuilder();
        report.AppendLine($"方法 {results.Length}（字节 {total}）：L3 无洞 {recovered.Length}（{(double)recovered.Length / Math.Max(1, results.Length):P1}，字节 {Fraction(Bytes(recovered)):P2}），写出 CIL {emitted.Count}（{(double)emitted.Count / Math.Max(1, results.Length):P1}，字节 {Fraction(Bytes(emitted)):P2}）");
        report.AppendLine("字节均按入口去重；各桶会重叠，不可直接相加。并集用于对账；“仅此”只看独立洞。");
        var buckets = results.Where(r => r.Body is null).Select(r => (Result: r,
            Categories: r.Holes.Where(h => !h.Derived).Select(h => Category(h.Reason)).Distinct().ToArray())).ToArray();
        report.AppendLine($"状态对账：洞 {buckets.Length} / {Bytes(buckets.Select(b => b.Result))} 字节；写出失败 {emitProblems.Count} / {Bytes(emitProblems.Keys)} 字节；已写出 {emitted.Count} / {Bytes(emitted)} 字节；入口并集 {bytes.Count} / {total} 字节");
        report.AppendLine();
        report.AppendLine("独立洞分桶：方法数 / 字节数 / 仅此方法数 / 仅此字节数 / 连带洞条数 / 桶");
        var derived = results.SelectMany(r => r.Holes).Where(h => h.Derived).GroupBy(h => Category(h.Reason)).ToDictionary(g => g.Key, g => g.Count());
        foreach (var group in buckets.SelectMany(b => b.Categories.Select(c => (Category: c, b.Result, Only: b.Categories.Length == 1)))
            .GroupBy(x => x.Category).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal))
        {
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(x => x.Result)),10} {group.Count(x => x.Only),7} {Bytes(group.Where(x => x.Only).Select(x => x.Result)),10} {derived.GetValueOrDefault(group.Key),8}  {group.Key}");
            foreach (var reason in group.SelectMany(x => x.Result.Holes.Where(h => !h.Derived && Category(h.Reason) == group.Key).Select(h => h.Reason)).GroupBy(r => r).OrderByDescending(r => r.Count()).Take(4))
                report.AppendLine($"           {reason.Count(),6}  {Shorten(reason.Key)}");
            derived.Remove(group.Key);
        }
        foreach (var (category, count) in derived.OrderBy(p => p.Key, StringComparer.Ordinal))
            report.AppendLine($"  {0,7} {0,10} {0,7} {0,10} {count,8}  {category}");
        report.AppendLine($"独立洞并集：{buckets.Count(b => b.Categories.Length > 0)} 方法 / {Bytes(buckets.Where(b => b.Categories.Length > 0).Select(b => b.Result))} 字节");

        bool Incomplete(string category) => category is "泛型" or "签名" or "提升" or "L2";
        var incomplete = buckets.Where(b => b.Categories.Any(Incomplete)).ToArray();
        report.AppendLine();
        report.AppendLine($"不可继续：{incomplete.Length} 方法 / {Bytes(incomplete.Select(b => b.Result))} 字节（泛型、签名、提升、L2 错误；洞集合不完整，不参与解锁与贪心）");
        foreach (var group in incomplete.SelectMany(b => b.Categories.Where(Incomplete).Select(c => (Category: c, b.Result))).GroupBy(x => x.Category))
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(x => x.Result)),10}  {group.Key}");

        // L3 无洞而写出失败的空集合不能被算作任意桶的收益：把已知 L4 障碍作为单独的桶。
        var candidates = buckets.Where(b => b.Categories.Length > 0 && !b.Categories.Any(Incomplete))
            .Concat(emitProblems.Select(p => (Result: p.Key, Categories: new[] { "CIL/" + Category(p.Value) }))).ToArray();
        var categories = candidates.SelectMany(b => b.Categories).Distinct().Order(StringComparer.Ordinal).ToArray();
        var alreadyEmitted = emitted.Select(r => r.Entry).ToHashSet();
        long UnlockBytes(IEnumerable<MethodRecoveryResult> rows) => Bytes(rows.Where(r => !alreadyEmitted.Contains(r.Entry)));
        report.AppendLine();
        report.AppendLine("可解锁量（诊断上限；不含已写出入口的字节，修洞后仍可能暴露新洞或写出失败）：");
        report.AppendLine("只差这一桶：方法数 / 新增字节数 / 桶（CIL/ 前缀表示已知写出障碍）");
        foreach (var category in categories.Select(c => (Name: c, Rows: candidates.Where(b => b.Categories.All(x => x == c)).Select(b => b.Result).ToArray()))
            .OrderByDescending(c => UnlockBytes(c.Rows)).ThenBy(c => c.Name, StringComparer.Ordinal))
            report.AppendLine($"  {category.Rows.Length,7} {UnlockBytes(category.Rows),10}  {category.Name}");
        report.AppendLine("按字节贪心清桶（并列按桶名序数排序）：步 / 新清桶 / 累计方法数 / 累计新增字节数 / 范围字节占比");
        var cleared = new HashSet<string>();
        for (var step = 1; step <= Math.Min(10, categories.Length); step++)
        {
            var choice = categories.Where(c => !cleared.Contains(c)).Select(c => (Name: c,
                Rows: candidates.Where(b => b.Categories.All(x => x == c || cleared.Contains(x))).Select(b => b.Result).ToArray()))
                .OrderByDescending(c => UnlockBytes(c.Rows)).ThenBy(c => c.Name, StringComparer.Ordinal).First();
            cleared.Add(choice.Name);
            report.AppendLine($"  {step,2} {choice.Name}  {choice.Rows.Length,7} {UnlockBytes(choice.Rows),10} {Fraction(UnlockBytes(choice.Rows)):P2}");
        }
        report.AppendLine();
        report.AppendLine("CIL 写出失败：方法数 / 字节数 / 桶");
        foreach (var group in emitProblems.GroupBy(p => Category(p.Value)).OrderByDescending(g => g.Count()))
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(p => p.Key)),10}  {group.Key}  例：{Shorten(group.First().Value)}");
        return report;
    }

    /// <summary>方法体用到的构造，用于挑选竖切集合和覆盖统计。loop 为深度优先遍历中的回边。</summary>
    private static string[] Features(ManagedBody body)
    {
        var features = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var region in body.Regions) features.Add(region.Kind == ManagedRegionKind.Catch ? "eh-catch" : "eh-fault");
        if (body.Method.Method.Name == ".ctor") features.Add("ctor");
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            var feature = statement switch
            {
                ManagedStore { Target: FieldValue } => "field-store", ManagedStore { Target: StaticFieldValue } => "static-store",
                ManagedStore { Target: ArrayElementValue } => "array-store",
                ManagedCall c => c.Invocation.Virtual ? "callvirt" : "call",
                ManagedBranch => "branch", ManagedSwitch => "switch", ManagedThrow => "throw", ManagedRethrow => "rethrow", ManagedEndFault => "fault", ManagedHole => "hole", ManagedCheck => "check", ManagedReturn { Value: not null } => "return-value",
                _ => null,
            };
            if (feature is not null) features.Add(feature);
            var values = statement switch
            {
                // 写入目标本身不是读取
                ManagedStore s => ManagedValues.Children(s.Target).Append(s.Value),
                ManagedJump or ManagedBranch or ManagedSwitch => ManagedValues.CopiedValues(statement).Concat(ManagedValues.Of(statement)),
                _ => ManagedValues.Of(statement),
            };
            foreach (var value in values.SelectMany(ManagedValues.Walk))
            {
                feature = value switch
                {
                    FieldValue => "field-load", StaticFieldValue => "static-load", NewObjectValue => "newobj", DelegateValue => "delegate-new", NewArrayValue => "newarr",
                    ArrayElementValue => "array-load", ArrayLengthValue => "array-length", StringValue => "string", BoxValue => "box",
                    IsInstValue => "isinst", BinaryValue => "arith", ConversionValue => "convert", ChoiceValue => "select", ComparisonValue => "compare",
                    _ => null,
                };
                if (feature is not null) features.Add(feature);
                if (ManagedTypes.PrimitiveName(value.Type) is "Single" or "Double") features.Add("float");
            }
        }
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        if (body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).Any(e => !blocks.ContainsKey(e.Target)))
        {
            features.Add("invalid-control-flow");
            return features.ToArray();
        }
        var state = new Dictionary<ulong, bool>(); // false：在栈上，true：已完成
        bool Loop(ulong address)
        {
            state[address] = false;
            foreach (var target in blocks[address].Statements.SelectMany(s => ManagedValues.Edges(s).Select(e => e.Target)))
                if (state.TryGetValue(target, out var done) ? !done : Loop(target)) return true;
            state[address] = true;
            return false;
        }
        if (Loop(body.Blocks[0].Address)) features.Add("loop");
        return features.ToArray();
    }

    private static TypeDef Top(TypeDef type)
    {
        while (type.DeclaringType is not null) type = type.DeclaringType;
        return type;
    }

    private static bool InNamespaces(TypeDef type, string[] namespaces)
    {
        var ns = Top(type).Namespace;
        return namespaces.Any(n => ns == n || ns.StartsWith(n + ".", StringComparison.Ordinal));
    }

    private static string Category(string reason) => reason.Split(' ')[0];

    private static string Shorten(string text) => text.Length > 150 ? text[..150] + "…" : text;
}
