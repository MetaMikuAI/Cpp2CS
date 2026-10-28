using Cpp2CS.Pipeline;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Execution;

/// <summary>
/// 执行对照（方法级差分）：对清单中的每个方法（竖切清单，或 recover 输出目录中写出的全部方法）做 L3 恢复并写出 CIL，然后按若干个种子合成输入与环境，
/// 在同一份合成内存上分别解释 CIL、在 Unicorn 中执行原机器码，比较事件序列（分配、调用及实参、抛出、返回值）
/// 与每个事件发生时两侧写过的内存。判定：
/// verified：至少一个用例可比较且全部一致；mismatch：任一用例不一致；not-checkable：没有可比较的用例（附原因）。
/// 断言：清单中的方法全部写出 CIL，且没有 mismatch；目录模式还要求待执行 CIL 与磁盘写出的方法体逐项一致。
/// 环境变量 EXECUTION_VERBOSE=1 时打印不一致用例的两侧事件；EXECUTION_TRACE=0x地址 时打印该方法每个用例的 CIL 侧事件。
/// --mutants：另做变异测试，检验这个对照能否发现错误：逐个向写出的 CIL 注入小错误（翻转分支、交换运算、改常量与字符串、
/// 换字段、删去写入或调用），重跑全部用例；有用例不一致即为检出。等价变异（如被截掉的常量位）检不出是正常的，未检出的逐个列出。
/// </summary>
internal static partial class ExecutionCheck
{
    private const int Cases = 32;

    [Command("execute", "执行对照：原机器码（Unicorn）与写出的 CIL（解释执行）在同一合成内存上结果一致", Arguments = "<binary> <metadata> <竖切清单 或 recover 输出目录> [--mutants ...]")]
    public static int Run(string binary, string metadata, string slice, string[] options)
    {
        var mutate = options.Contains("--mutants");
        // 栈帧代表集合增加输入覆盖；同一组种子先验证未变异基线，再用于变异。
        // 多个布尔桩结果的合取可能遮蔽局部错误，不能只增加变异侧种子而误把模型差异算成检出。
        var caseCount = options.Contains("--frame-mutants") ? 128 : Cases;
        // --shard k/n：只检查序号模 n 余 k 的方法（多进程并行，见 tests/execute_sharded.py）。恢复与写出 CIL 仍对全部方法进行：
        // 构造函数能否写出取决于同类型的其他构造函数（ConstructorInitialization），只写出一部分会改变被检查的方法体
        var (shard, shards) = options.SkipWhile(o => o != "--shard").Skip(1).FirstOrDefault() is { } spec
            ? (int.Parse(spec.Split('/')[0]), int.Parse(spec.Split('/')[1])) : (0, 1);
        // --only <清单>：只对清单中的方法（制表符分隔：入口、方法名）做对照，恢复与写出 CIL 仍对全部方法进行。
        // 重构中用来只检查 CIL 有变化或新写出的方法（快速档 tests/quick.sh）。结果写入 execution-only.tsv，不覆盖全量的 execution.tsv。
        var only = options.SkipWhile(o => o != "--only").Skip(1).FirstOrDefault() is { } onlyPath
            ? File.ReadLines(onlyPath).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t'))
                .Select(f => (Convert.ToUInt64(f[0], 16), f[1])).ToHashSet()
            : null;
        bool Selected(MethodRecoveryResult result, int i) => i % shards == shard && (only is null || only.Contains((result.Entry, result.Method.ToString())));
        // 参数是 recover 的输出目录时取其中写出的全部方法，逐方法的结果写入该目录的 execution.tsv（分片时为 execution-k-of-n.tsv），控制台只列出未通过的方法
        var full = Directory.Exists(slice);
        var bytes = full ? ReadBytes(Path.Combine(slice, "recovery.jsonl")) : new Dictionary<ulong, long>();
        var facts = FactsBuilder.Build(binary, metadata);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var methods = full ? ReadList(facts, Path.Combine(slice, "emitted.tsv"), 3, 4) : ReadList(facts, slice, 0, 1);
        var recovery = new MethodRecovery(facts, types);
        var instances = methods.ToDictionary(t => t.Method.Method, t => t.Instance);
        var results = methods.Select(t => t.Entry == 0 ? new MethodRecoveryResult(t.Method, 0, null, [new(0, "语言定义 待核对元数据证据")])
            : t.Recover(recovery)).ToArray();
        if (only is not null && only.Except(results.Select(r => (r.Entry, r.Method.ToString()))).Any())
            throw new InvalidDataException("--only 含未匹配方法；请使用写出清单中的入口与开放泛型方法名");
        if (full) AutoPropertyManifest.RestoreSynthesized(slice, types, results);
        var skeleton = new Skeleton(facts.Model);
        skeleton.ApplyDeclarations(results);
        if (full)
            foreach (var line in File.ReadLines(Path.Combine(slice, "recovery.jsonl")))
            {
                using var declaration = JsonDocument.Parse(line);
                var row = declaration.RootElement;
                if (!row.TryGetProperty("declaration", out var kind) || kind.GetString() != "PlatformInvoke") continue;
                var target = RecoveryTarget.Find(facts, Convert.ToUInt64(row.GetProperty("address").GetString(), 16), row.GetProperty("method").GetString()!);
                var recovered = target.Recover(recovery);
                if (recovered.PlatformImport is null) throw new InvalidDataException("原生导入声明未复现");
                skeleton.ApplyDeclarations([recovered]);
            }
        var emitter = new BodyEmitter(skeleton, types);
        var closure = new AccessorRecovery(facts, types, new MethodSummaryService(recovery), emitter, results, full ? AutoPropertyManifest.ReadRejected(Path.Combine(slice, "autoprop-rejected-input.tsv")) : null);
        skeleton.ApplyDeclarations(closure.All);
        var index = new WorldIndex(facts, types);
        if (options.Contains("--concrete-generics"))
            foreach (var result in results.Where(Selected))
                instances[result.Method.Method] = ConcreteGenericInput(instances[result.Method.Method], result.Entry, index);
        var cecil = new CecilModel(facts.Model, skeleton);
        var interpreter = new CilInterpreter(cecil, index);
        using var machine = new NativeMachine(facts);
        var a = new Assertions();
        var candidates = full ? EvidenceCandidates(slice, facts, types, results, skeleton) : closure.Candidates;
        var evidencePath = Path.Combine(slice, "accessor-evidence-input.tsv");
        var evidence = full && File.Exists(evidencePath) ? AccessorEvidence.Read(evidencePath) : new HashSet<string>();
        if (!full)
            foreach (var candidate in candidates.Values)
            {
                if (candidate.LanguageDefined && candidate.Method.Method.Address == 0) continue;
                var outcome = Check(candidate.Method, skeleton, cecil, interpreter, machine, index, false);
                a.True(outcome.Verdict == "verified" && outcome.Matches == Cases, $"访问器先独立 verified：{candidate.Method} {outcome.Detail}");
                if (outcome.Verdict == "verified" && outcome.Matches == Cases) evidence.Add(AccessorEvidence.Describe(facts, skeleton, candidate));
            }
        // 内联认回的被调方法：全量时取 recover 写下的候选；竖切时先独立验证（同 F9 访问器）。
        var inlinePath = Path.Combine(slice, "inline-candidates.tsv");
        var inlineCandidates = full ? (File.Exists(inlinePath) ? File.ReadLines(inlinePath).Where(l => l.Length > 0).ToHashSet(StringComparer.Ordinal) : [])
            : closure.InlineCandidates.Values.Select(r => AccessorEvidence.Describe(facts, skeleton, r.Method)).ToHashSet(StringComparer.Ordinal);
        if (!full)
            foreach (var candidate in closure.InlineCandidates.Values)
            {
                var outcome = Check(candidate.Method, skeleton, cecil, interpreter, machine, index, false);
                Console.WriteLine($"  内联认回候选 {candidate.Method}：{outcome.Verdict} {outcome.Matches}/{Cases}{outcome.Detail}");
                if (outcome.Verdict == "verified" && outcome.Matches == Cases) evidence.Add(AccessorEvidence.Describe(facts, skeleton, candidate.Method));
            }
        closure.Rewrite(types, emitter, c => evidence.Contains(AccessorEvidence.Describe(facts, skeleton, c)),
            m => evidence.Contains(AccessorEvidence.Describe(facts, skeleton, new MethodRef(m, [], []))));
        var problems = closure.Problems;
        if (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1")
        {
            Console.Error.WriteLine($"  [写出] 结果 {closure.All.Count()}，有方法体 {closure.All.Count(r => r.Body is not null)}，问题 {problems.Count}；{string.Join(" ", closure.All.Select(r => $"0x{r.Entry:x}:{r.Body?.Regions.Count}:{skeleton.Method(r.Method.Method).Body.Instructions.Count}"))}");
            foreach (var result in closure.All.Where(r => r.Body is null || problems.ContainsKey(r.Body)))
                Console.Error.WriteLine($"  [未写出] 0x{result.Entry:x} {result.Method}：{(result.Body is null ? string.Join("；", result.Holes.Take(2).Select(h => h.Reason)) : problems[result.Body])}");
        }
        interpreter.SetAccessors(emitter, skeleton);
        if (full) EmittedBodyCheck.AssertSame(slice, results.Where(Selected), skeleton);
        var dependencyMethods = full ? File.ReadLines(Path.Combine(slice, "emitted.tsv")).Select(l => l.Split('\t'))
            .Where(f => f.Length > 6 && f[6] == "dependency").Select(f => (Convert.ToUInt64(f[3], 16), f[4])).ToHashSet() : [];
        var targetEntries = full ? TargetEntries(Path.Combine(slice, "recovery.jsonl")) : [];
        var targetBytes = bytes.Where(p => targetEntries.Contains(p.Key)).ToDictionary();
        var verifiedAccessors = new List<string>();
        var verbose = Environment.GetEnvironmentVariable("EXECUTION_VERBOSE") == "1";

        var verdicts = new Dictionary<string, int>();
        var dependencyVerdicts = new Dictionary<string, int>();
        var verdictEntries = new Dictionary<string, HashSet<ulong>>();
        var reasons = new Dictionary<string, (int Count, string Example)>();
        var mutants = new Dictionary<string, string>();
        var delegateMutants = new Dictionary<string, string>();
        var accessorMutants = new Dictionary<string, string>();
        var exceptionMutants = new Dictionary<string, string>();
        var exceptionMethods = 0;
        var thrownCases = 0;
        var tableName = only is not null
            ? shards == 1 ? "execution-only.tsv" : $"execution-only-{shard}-of-{shards}.tsv"
            : shards == 1 ? "execution.tsv" : $"execution-{shard}-of-{shards}.tsv";
        // 逐方法落盘，保留长时间变异检查之前已完成的判定；定向分片使用独立文件。
        using var table = full ? new StreamWriter(Path.Combine(slice, tableName)) { AutoFlush = true } : null;
        var clock = System.Diagnostics.Stopwatch.StartNew();
        var done = 0;
        var baselineAccessorCalls = 0;
        var baselineNullCalls = 0;
        var selectedCount = results.Where(Selected).Count();
        foreach (var result in results.Where(Selected))
        {
            ++done;
            if (only is not null || done % 500 == 0) Console.Error.WriteLine($"  {done}/{selectedCount}，{clock.Elapsed.TotalMinutes:F1} 分钟，0x{result.Entry:x} {result.Method}");
            var name = $"0x{result.Entry:x} {result.Method}";
            if (result.Body is null || problems.ContainsKey(result.Body))
            {
                var reason = result.Body is null ? string.Join("；", result.Holes.Select(h => h.Reason).Distinct()) : problems[result.Body].Message;
                a.True(false, $"{name} 没有写出 CIL：{reason}");
                continue;
            }
            var callsBefore = interpreter.AccessorCalls;
            var nullBefore = interpreter.NullAccessorCalls;
            Outcome outcome;
            try
            {
                outcome = result.Entry == 0 && candidates.GetValueOrDefault(result.Method.Method) is { LanguageDefined: true }
                    ? new Outcome("language-defined", 0, 0, "自动属性语言定义；无原生代码，未执行对照")
                    : Check(instances[result.Method.Method], skeleton, cecil, interpreter, machine, index, verbose, caseCount, result.Entry);
            }
            catch (InferredCallError e)
            {
                a.True(false, $"{name} F8 运行时身份核对失败：{e.Message}");
                outcome = new Outcome("not-checkable", 0, 0, e.Message, "对照器错误 F8身份");
            }
            catch (Exception e) when (e is not Unsupported)
            {
                // 对照器自身的缺陷：不中断全量运行，单独计数
                outcome = new Outcome("not-checkable", 0, 0, $"；对照器异常 {e.GetType().Name}：{e.Message}{(verbose ? "\n" + e.StackTrace : "")}", $"对照器异常 {e.GetType().Name}");
            }
            baselineAccessorCalls += interpreter.AccessorCalls - callsBefore;
            if (skeleton.Method(result.Method.Method).Body.HasExceptionHandlers)
            {
                exceptionMethods++;
                thrownCases += outcome.ThrowCases;
                a.True(outcome.Verdict == "verified" && outcome.Matches == Cases, $"{name} 异常方法必须全部 {Cases} 个用例可比较且一致");
            }
            baselineNullCalls += interpreter.NullAccessorCalls - nullBefore;
            if (outcome.Verdict == "verified" && outcome.Matches == Cases && candidates.TryGetValue(result.Method.Method, out var accessor))
                verifiedAccessors.Add(AccessorEvidence.Describe(facts, skeleton, accessor));
            if (outcome.Verdict == "verified" && outcome.Matches == Cases && result.Method.Method.Address != 0 && inlineCandidates.Count > 0
                && AccessorEvidence.Describe(facts, skeleton, result.Method) is var inlineEvidence && inlineCandidates.Contains(inlineEvidence))
                verifiedAccessors.Add(inlineEvidence);
            var dependency = dependencyMethods.Contains((result.Entry, result.Method.ToString()));
            var counts = dependency ? dependencyVerdicts : verdicts;
            counts[outcome.Verdict] = counts.GetValueOrDefault(outcome.Verdict) + 1;
            if (!dependency)
            {
                if (!verdictEntries.TryGetValue(outcome.Verdict, out var entries)) verdictEntries[outcome.Verdict] = entries = [];
                entries.Add(result.Entry);
            }
            if (outcome.Verdict == "not-checkable")
                reasons[outcome.Reason] = (reasons.GetValueOrDefault(outcome.Reason).Count + 1, reasons.GetValueOrDefault(outcome.Reason).Example ?? name);
            var mark = outcome.Verdict switch { "verified" => "✓", "mismatch" => "✗", _ => "?" };
            var line = $"{name}：一致 {outcome.Matches}/{caseCount}，覆盖 {outcome.Coverage:P0}{outcome.Detail}";
            if (!full || outcome.Verdict != "verified") Console.WriteLine($"  {mark} {line}");
            table?.WriteLine($"0x{result.Entry:x}\t{result.Method}\t{outcome.Verdict}\t{outcome.Matches}\t{outcome.Coverage:F3}\t{outcome.Reason}\t{outcome.Detail.TrimStart('；')}\t{bytes[result.Entry]}\t{(dependency ? "dependency" : "target")}\t{outcome.ThrowCases}\t{skeleton.Method(result.Method.Method).Body.ExceptionHandlers.Count}");
            a.True(!outcome.Reason.StartsWith("对照器异常", StringComparison.Ordinal), $"{name} {outcome.Reason}");
            a.True(outcome.Verdict != "mismatch", $"{name} 执行结果不一致");
            if (options.Contains("--frame-mutants"))
                a.True(outcome.Verdict == "verified" && outcome.Matches == caseCount, $"{name} 栈帧变异基线必须全部 {caseCount} 个用例一致");
            if (mutate && HasDelegateBody(skeleton.Method(result.Method.Method)))
                a.True(outcome.Verdict == "verified" && outcome.Matches == caseCount, $"{name} 委托变异基线必须全部 {caseCount} 个用例可比较且一致");
            if (mutate && outcome.Verdict == "verified")
            {
                var methodMutants = new Dictionary<string, string>();
                Mutate(instances[result.Method.Method], result.Entry, skeleton, cecil, interpreter, machine, index, methodMutants, emitter.ExplicitInitializations, caseCount);
                foreach (var pair in methodMutants) mutants.Add(pair.Key, pair.Value);
                if (skeleton.Method(result.Method.Method).Body.HasExceptionHandlers)
                    foreach (var pair in methodMutants) exceptionMutants.Add(pair.Key, pair.Value);
                foreach (var pair in methodMutants.Where(p => p.Key.Contains("F9 ", StringComparison.Ordinal))) accessorMutants.Add(pair.Key, pair.Value);
                if (HasDelegateBody(skeleton.Method(result.Method.Method)))
                    foreach (var pair in methodMutants) delegateMutants.Add(pair.Key, pair.Value);
            }
        }
        Console.WriteLine($"  F8 运行时身份核对通过 {machine.InferredIdentityChecks} 次");
        Console.WriteLine($"  原生泛型虚方法实例化 {machine.GenericVirtualResolutions} 次");
        Console.WriteLine($"  F5 异常方法 {exceptionMethods}，两侧实际注入抛出 {thrownCases}/{exceptionMethods * Cases} 用例");
        if (full)
        {
            long Size(string verdict) => verdictEntries.TryGetValue(verdict, out var entries) ? entries.Where(targetBytes.ContainsKey).Sum(e => targetBytes[e]) : 0;
            Console.WriteLine($"  判定：{string.Join("，", new[] { "verified", "mismatch", "not-checkable" }.Select(v => $"{v} {verdicts.GetValueOrDefault(v)} 方法 / {Size(v)} 字节"))}（{clock.Elapsed.TotalMinutes:F1} 分钟）");
            Console.WriteLine($"  依赖访问器：{string.Join("，", dependencyVerdicts.Select(p => $"{p.Key} {p.Value}"))}");
            Console.WriteLine($"  已验证字节：{Size("verified")} / {targetBytes.Values.Sum()} = {(double)Size("verified") / Math.Max(1, targetBytes.Values.Sum()):P4}（范围与各判定均按入口去重）");
        }
        else Console.WriteLine($"  判定：{string.Join("，", verdicts.OrderBy(v => v.Key).Select(v => $"{v.Key} {v.Value}"))}（{clock.Elapsed.TotalMinutes:F1} 分钟）");
        if (full) AccessorEvidence.Write(Path.Combine(slice, shards == 1 ? "accessor-verified.tsv" : $"accessor-verified-{shard}-of-{shards}.tsv"), verifiedAccessors);
        Console.WriteLine($"  F9 基线透明调用 {baselineAccessorCalls} 次，其中 null 接收者 {baselineNullCalls} 次（不含变异）");
        foreach (var (reason, (count, example)) in reasons.OrderByDescending(r => r.Value.Count))
            Console.WriteLine($"    不可检查 {count,5}  {reason}（例 {example}）");
        if (mutate)
        {
            var detected = mutants.Count(m => m.Value == "检出");
            var missed = mutants.Where(m => m.Value == "未检出").Select(m => m.Key).ToArray();
            Console.WriteLine($"  变异：{mutants.Count} 个，检出 {detected}，未检出 {missed.Length}，不可比较 {mutants.Count(m => m.Value == "不可比较")}，"
                + $"非法 IL {mutants.Count(m => m.Value == "非法 IL")}；"
                + $"检出率 {(double)detected / Math.Max(1, detected + missed.Length):P1}");
            foreach (var m in missed) Console.WriteLine($"    未检出：{m}");
            CheckDelegateMutants(a, delegateMutants);
            CheckAccessorMutants(a, accessorMutants);
            if (exceptionMethods > 0)
            {
                var caught = exceptionMutants.Count(p => p.Value == "检出");
                var missedExceptions = exceptionMutants.Count(p => p.Value == "未检出");
                Console.WriteLine($"  F5 异常方法变异 {exceptionMutants.Count}，检出 {caught}，未检出 {missedExceptions}");
                a.True(caught + missedExceptions > 0 && caught * 100 >= 95 * (caught + missedExceptions), "F5 异常方法变异检出率至少 95%");
                a.True(exceptionMutants.All(p => p.Value is "检出" or "未检出"), "F5 异常变异全部可比较且 IL 合法");
                var operators = exceptionMutants.Where(p => p.Key.Contains("F5 ", StringComparison.Ordinal)).ToArray();
                var operatorHits = operators.Count(p => p.Value == "检出");
                Console.WriteLine($"  F5 异常专用变异 {operators.Length}，检出 {operatorHits}");
                a.True(operators.Length > 0 && operatorHits * 100 >= 95 * operators.Length, "F5 异常专用变异检出率至少 95%（不可比较与非法 IL 也计失败）");
            }
            if (!full) a.True((double)detected / Math.Max(1, detected + missed.Length) >= 0.95, "竖切变异检出率至少 95%");
            if (options.SkipWhile(o => o != "--mutant-report").Skip(1).FirstOrDefault() is { } report)
                File.WriteAllLines(report, mutants.OrderBy(p => p.Key, StringComparer.Ordinal).Select(p => $"{p.Value}\t{p.Key}"));
            a.True(detected * 100 >= 95 * (detected + missed.Length), "变异检出率至少 95%");
            var leafMutants = mutants.Where(m => m.Key.Contains("结构体：", StringComparison.Ordinal)).ToArray();
            if (options.Contains("--frame-mutants"))
                foreach (var kind in new[] { "换叶子", "交换叶子写入", "漏掉 initobj" })
                    a.True(leafMutants.Any(m => m.Key.Contains("结构体：" + kind + " ", StringComparison.Ordinal)), $"栈帧集合必须覆盖变异 {kind}");
            if (leafMutants.Length > 0)
            {
                var caught = leafMutants.Count(m => m.Value == "检出");
                var missedLeaves = leafMutants.Count(m => m.Value == "未检出");
                Console.WriteLine($"  结构体叶子变异：{leafMutants.Length} 个，检出 {caught}，未检出 {missedLeaves}");
                a.True(caught * 100 >= 95 * (caught + missedLeaves), "结构体叶子变异检出率至少 95%");
            }
        }
        return a.Finish("execute");
    }

    private static HashSet<ulong> TargetEntries(string path)
    {
        var entries = new HashSet<ulong>();
        foreach (var line in File.ReadLines(path))
        {
            using var document = JsonDocument.Parse(line);
            var row = document.RootElement;
            if (!row.TryGetProperty("dependency", out var dependency) || !dependency.GetBoolean())
                entries.Add(Convert.ToUInt64(row.GetProperty("address").GetString(), 16));
        }
        return entries;
    }

    private static Dictionary<ulong, long> ReadBytes(string path)
    {
        var bytes = new Dictionary<ulong, long>();
        foreach (var line in File.ReadLines(path))
        {
            using var document = JsonDocument.Parse(line);
            var row = document.RootElement;
            var entry = Convert.ToUInt64(row.GetProperty("address").GetString(), 16);
            var size = row.GetProperty("bytes").GetInt64();
            if ((entry == 0 ? size != 0 || !row.GetProperty("dependency").GetBoolean() : size <= 0)
                || bytes.TryGetValue(entry, out var previous) && previous != size)
                throw new InvalidDataException($"{path}: 0x{entry:x} 的函数字节数不一致或非正数");
            bytes[entry] = size;
        }
        return bytes;
    }

    /// <summary>对一个方法逐个应用变异、跑全部用例、复原。</summary>
    private static void Mutate(MethodRef tested, ulong entry, Skeleton skeleton, CecilModel cecil, CilInterpreter interpreter, NativeMachine machine, WorldIndex index, Dictionary<string, string> results, IReadOnlySet<Instruction> initializations, int caseCount)
    {
        var definition = skeleton.Method(tested.Method);
        var signature = index.StructAbi.Signature(tested);
        var statics = interpreter.ExpandedInstructions(definition)
            .Where(i => i.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda).Select(i => cecil.Field((Mono.Cecil.FieldReference)i.Operand))
            .Concat(interpreter.IntrinsicStatics(definition)).Distinct().ToArray();
        var hints = HintsOf(definition, cecil);
        var throwPlans = ThrowPlans(tested, definition, cecil, interpreter, index, caseCount: caseCount);
        var mutationCases = Enumerable.Range(0, caseCount).Select(seed => (Seed: seed, Plan: throwPlans[seed])).ToList();
        var allCallPlans = ThrowPlans(tested, definition, cecil, interpreter, index, preferProtected: false, caseCount: caseCount);
        // 注入会截断原来的正常路径。变异还覆盖同一种子的未注入版本，但必须先证明
        // 未变异的两侧一致，不能把新增输入上的恢复错误冒充变异检出。
        for (var seed = 0; seed < caseCount; seed++)
        {
            if (throwPlans[seed] is null) continue;
            // 除 try 内计划外，保留全调用序列的计划，覆盖前导/续接点和调用次序变化。
            foreach (var plan in new ThrowPlan?[] { null, allCallPlans[seed] }.Distinct())
            {
                if (plan == throwPlans[seed]) continue;
                var world = new World(index, seed, hints, InitializedOwner(tested)) { ThrowPlan = plan };
                foreach (var field in statics) world.PrepareStatic(field);
                var (bits, values) = Arguments(world, interpreter, tested, signature);
                var cil = interpreter.Run(world, definition, tested, values);
                var native = machine.Run(world, tested, signature, bits, cil.Callees, entry);
                if (Trace.Difference(world, native, cil) is { } difference)
                    throw new InvalidOperationException($"F5 附加基线不一致：{tested} 种子 {seed} 计划 {plan}：{difference}");
                mutationCases.Add((seed, plan));
            }
        }
        foreach (var (description, apply, revert) in ShapeModels.Mutate(new MutationSite(definition, cecil, index, initializations, interpreter)))
        {
            apply();
            var verdict = "不可比较";
            try
            {
                foreach (var (seed, plan) in mutationCases)
                {
                    if (verdict is "检出" or "非法 IL") break;
                    var world = new World(index, seed, hints, InitializedOwner(tested)) { ThrowPlan = plan };
                    try
                    {
                        foreach (var field in statics) world.PrepareStatic(field);
                        var (bits, values) = Arguments(world, interpreter, tested, signature);
                        var cil = interpreter.Run(world, definition, tested, values);
                        var native = machine.Run(world, tested, signature, bits, cil.Callees, entry);
                        verdict = Trace.Difference(world, native, cil) is null ? "未检出" : "检出";
                    }
                    catch (InferredCallError) { verdict = "检出"; }
                    catch (Unsupported) { }
                    catch (Exception e) when (e is InvalidOperationException or InvalidCastException or IndexOutOfRangeException)
                    {
                        // 栈失衡、操作数类型不符：变异后的 IL 不合法（ILVerify 会拒绝），不计入检出率
                        verdict = "非法 IL";
                        break;
                    }
                }
            }
            finally { revert(); }
            results[$"0x{entry:x} {tested}: {description}"] = verdict;
        }
    }

    /// <summary>就地变异（每个返回应用与复原两个动作）。</summary>
    [MutationFamily("CIL 基本语义", 10)]
    private static IEnumerable<(string, Action, Action)> BasicMutations(MutationSite site) => Mutations(site.Method);

    private static IEnumerable<(string, Action, Action)> Mutations(Mono.Cecil.MethodDefinition method)
    {
        var il = method.Body.GetILProcessor();
        var instructions = method.Body.Instructions.ToArray();
        for (var position = 0; position < instructions.Length; position++)
        {
            var instruction = instructions[position];
            var code = instruction.OpCode;
            var operand = instruction.Operand;
            var at = $"#{position}（后接 {(position + 1 < instructions.Length ? instructions[position + 1].OpCode : "")}）";
            OpCode? swapped = code.Code switch
            {
                Code.Brtrue => OpCodes.Brfalse, Code.Brfalse => OpCodes.Brtrue, Code.Add => OpCodes.Sub, Code.Sub => OpCodes.Add,
                Code.Clt => OpCodes.Cgt, Code.Cgt => OpCodes.Clt, Code.Clt_Un => OpCodes.Cgt_Un, Code.Cgt_Un => OpCodes.Clt_Un,
                Code.And => OpCodes.Or, Code.Or => OpCodes.And, Code.Mul => OpCodes.Add, Code.Shl => OpCodes.Shr_Un, Code.Shr_Un => OpCodes.Shl,
                _ => null,
            };
            if (swapped is { } op) yield return ($"{at} {code} → {op}", () => instruction.OpCode = op, () => instruction.OpCode = code);
            if (code.Code is >= Code.Ldc_I4_M1 and <= Code.Ldc_I4)
            {
                var value = code.Code switch { Code.Ldc_I4_M1 => -1, Code.Ldc_I4_S => (sbyte)operand, Code.Ldc_I4 => (int)operand, _ => code.Code - Code.Ldc_I4_0 };
                yield return ($"{at} 常量 {value} → {value + 1}", () => { instruction.OpCode = OpCodes.Ldc_I4; instruction.Operand = value + 1; },
                    () => { instruction.OpCode = code; instruction.Operand = operand; });
            }
            if (code.Code == Code.Ldc_R4)
                yield return ($"{at} 常量 {operand} + 1", () => instruction.Operand = (float)operand + 1, () => instruction.Operand = operand);
            if (code.Code == Code.Ldstr)
                yield return ($"{at} 字符串 \"{operand}\" + \"!\"", () => instruction.Operand = (string)operand + "!", () => instruction.Operand = operand);
            if (code.Code is Code.Ldfld or Code.Stfld && operand is Mono.Cecil.FieldReference field && field.Resolve() is { } resolved
                && !resolved.DeclaringType.IsValueType
                && resolved.DeclaringType.Fields.FirstOrDefault(f => f != resolved && !f.IsStatic && f.FieldType.FullName == resolved.FieldType.FullName) is { } other)
            {
                var replacement = new Mono.Cecil.FieldReference(other.Name, field.FieldType, field.DeclaringType);
                yield return ($"{at} {code} {field.Name} → {other.Name}", () => instruction.Operand = replacement, () => instruction.Operand = operand);
            }
            if (code.Code == Code.Stfld)
            {
                var extra = il.Create(OpCodes.Pop);
                yield return ($"{at} 删去 stfld {((Mono.Cecil.FieldReference)operand).Name}",
                    () => { instruction.OpCode = OpCodes.Pop; instruction.Operand = null; il.InsertAfter(instruction, extra); },
                    () => { il.Remove(extra); instruction.OpCode = code; instruction.Operand = operand; });
            }
            if (code.Code is Code.Call or Code.Callvirt && operand is Mono.Cecil.MethodReference callee && callee.ReturnType.MetadataType == Mono.Cecil.MetadataType.Void)
            {
                var count = callee.Parameters.Count + (callee.HasThis ? 1 : 0);
                if (count == 0) continue;
                var extras = Enumerable.Range(0, count - 1).Select(_ => il.Create(OpCodes.Pop)).ToArray();
                yield return ($"{at} 删去调用 {callee.Name}",
                    () => { instruction.OpCode = OpCodes.Pop; instruction.Operand = null; foreach (var e in extras) il.InsertAfter(instruction, e); },
                    () => { foreach (var e in extras) il.Remove(e); instruction.OpCode = code; instruction.Operand = operand; });
            }
            // F1 尾调用的结果被丢弃时，必须检验调用事件本身。按签名弹出实参，并同时删去原 pop，保持栈平衡。
            // 依据 ECMA-335 III.3.19/3.54；仅生成故意错误的 CIL，不改变原生侧、解释器或比较规则。
            if (code.Code is Code.Call or Code.Callvirt && operand is Mono.Cecil.MethodReference discarded
                && discarded.ReturnType.MetadataType != Mono.Cecil.MetadataType.Void
                && position + 1 < instructions.Length && instructions[position + 1].OpCode.Code == Code.Pop)
            {
                var pop = instructions[position + 1];
                var count = discarded.Parameters.Count + (discarded.HasThis ? 1 : 0);
                var extras = Enumerable.Range(0, Math.Max(0, count - 1)).Select(_ => il.Create(OpCodes.Pop)).ToArray();
                yield return ($"{at} 删去被丢弃结果的调用 {discarded.Name}",
                    () =>
                    {
                        instruction.OpCode = count == 0 ? OpCodes.Nop : OpCodes.Pop;
                        instruction.Operand = null;
                        pop.OpCode = OpCodes.Nop;
                        foreach (var e in extras) il.InsertAfter(instruction, e);
                    },
                    () =>
                    {
                        foreach (var e in extras) il.Remove(e);
                        instruction.OpCode = code;
                        instruction.Operand = operand;
                        pop.OpCode = OpCodes.Pop;
                    });
            }

        }
    }

    /// <summary>Reason：不可检查时的主要原因（用例最多的一类，去掉具体类型与方法名以便汇总）。</summary>
    private sealed record Outcome(string Verdict, int Matches, double Coverage, string Detail, string Reason = "", int ThrowCases = 0);

    private static Outcome Check(MethodRef tested, Skeleton skeleton, CecilModel cecil, CilInterpreter interpreter, NativeMachine machine, WorldIndex index, bool verbose, int caseCount = Cases, ulong? nativeEntry = null)
    {
        cecil.Context = tested;
        var definition = skeleton.Method(tested.Method);
        var entry = nativeEntry ?? tested.Method.Address;
        var function = index.Facts.Code.At(entry)!;
        var signature = index.StructAbi.Signature(tested);
        var statics = interpreter.ExpandedInstructions(definition)
            .Where(i => i.OpCode.Code is Code.Ldsfld or Code.Stsfld or Code.Ldsflda).Select(i => cecil.Field((Mono.Cecil.FieldReference)i.Operand))
            .Concat(interpreter.IntrinsicStatics(definition)).Distinct().ToArray();
        var hints = HintsOf(definition, cecil);
        machine.Covered.Clear();
        var throwPlans = ThrowPlans(tested, definition, cecil, interpreter, index, caseCount: caseCount);
        var throwCases = 0;
        var matches = 0;
        var mismatches = new List<string>();
        var unsupported = new Dictionary<string, int>();
        HashSet<Instruction>? arrayAccesses = Environment.GetEnvironmentVariable("EXECUTION_ARRAY_COVERAGE") == "1" ? [] : null;
        HashSet<Instruction> arrayInstructions = arrayAccesses is null ? [] : definition.Body.Instructions.Where(i => i.OpCode.Code is Code.Ldelem_Any or Code.Stelem_Any).ToHashSet();
        var arrayCases = 0;
        var returns = 0;
        for (var seed = 0; seed < caseCount; seed++)
        {
            var world = new World(index, seed, hints, InitializedOwner(tested)) { ThrowPlan = throwPlans[seed] };
            try
            {
                foreach (var field in statics) world.PrepareStatic(field);
                var (bits, values) = Arguments(world, interpreter, tested, signature);
                var cil = interpreter.Run(world, definition, tested, values);
                var native = machine.Run(world, tested, signature, bits, cil.Callees, entry);
                if (arrayAccesses is not null)
                {
                    var completed = cil.ArrayAccesses!.Where(arrayInstructions.Contains).ToArray();
                    arrayAccesses.UnionWith(completed);
                    if (completed.Length > 0) arrayCases++;
                    if (cil.Result?.StartsWith("return ", StringComparison.Ordinal) == true) returns++;
                }
                if (native.PlannedThrowReached && cil.PlannedThrowReached) throwCases++;
                if (Environment.GetEnvironmentVariable("EXECUTION_TRACE") == $"0x{tested.Method.Address:x}")
                    Console.WriteLine($"    种子 {seed}：{string.Join(" | ", cil.Events.Select(e => e.Text))}");
                if (Trace.Difference(world, native, cil) is { } difference)
                {
                    mismatches.Add($"种子 {seed}：{difference}");
                    if (verbose)
                    {
                        Console.WriteLine($"    种子 {seed} 原生：{string.Join(" | ", native.Events.Select(e => e.Text))}");
                        Console.WriteLine($"    种子 {seed} CIL ：{string.Join(" | ", cil.Events.Select(e => e.Text))}");
                    }
                }
                else matches++;
            }
            catch (Unsupported e)
            {
                unsupported[e.Message] = unsupported.GetValueOrDefault(e.Message) + 1;
            }
        }
        var covered = machine.Covered.Sum(b => (long)b.Size);
        if (arrayAccesses is not null)
            Console.WriteLine($"ARRAY_COVERAGE\t0x{tested.Method.Address:x}\t{tested}\t{arrayAccesses.Count(i => i.OpCode.Code == Code.Ldelem_Any)}\t{arrayInstructions.Count(i => i.OpCode.Code == Code.Ldelem_Any)}\t{arrayAccesses.Count(i => i.OpCode.Code == Code.Stelem_Any)}\t{arrayInstructions.Count(i => i.OpCode.Code == Code.Stelem_Any)}\t{arrayCases}\t{returns}\t{caseCount}");
        var coverage = (double)Math.Min(covered, (long)function.Size) / function.Size;
        var detail = (mismatches.Count > 0 ? $"；不一致 {mismatches.Count}，首例 {mismatches[0]}" : "")
            + (unsupported.Count > 0 ? $"；不可检查 {unsupported.Values.Sum()}（{string.Join("；", unsupported.OrderByDescending(u => u.Value).Take(3).Select(u => $"{u.Value}× {u.Key}"))}）" : "");
        var verdict = mismatches.Count > 0 ? "mismatch" : matches > 0 ? "verified" : "not-checkable";
        var reason = verdict == "not-checkable" && unsupported.Count > 0 ? Category(unsupported.MaxBy(u => u.Value).Key) : "";
        return new Outcome(verdict, matches, coverage, detail, reason, throwCases);
    }

    /// <summary>不可检查原因的类别：去掉其中的类型、方法、地址等具体部分。</summary>
    private static string Category(string reason)
    {
        var text = System.Text.RegularExpressions.Regex.Replace(reason, @"0x[0-9a-f]+", "#");
        // 原因的格式多为"描述 具体对象"或"描述 具体对象：细节"：类型名、方法名中含有 '.'、'<'，按词去掉
        var words = text.Split(' ').Select(w => w.Contains('.') || w.Contains('<') || w.Contains('`') ? "…" : w);
        return string.Join(' ', words);
    }

    /// <summary>
    /// 被测方法执行时必定已初始化的类型（按解释器采用的触发点，见 CilInterpreter.Invoke）：自身的静态构造正在运行；
    /// 静态方法、构造函数（经 newobj 时分配函数已初始化，经 base(...) 时调用前已初始化）与值类型的方法在进入前初始化；
    /// 精确初始化的类型有实例即已初始化。beforefieldinit 引用类型的实例方法保留尚未初始化的情形（this 可能是子类的实例）。
    /// </summary>
    private static TypeRef? InitializedOwner(MethodRef tested) =>
        tested.Method.IsStatic || tested.Method.Name == ".ctor" || World.Precise(tested.DeclaringType)
            || tested.DeclaringType is DefinitionRef { Definition.IsValueType: true } ? tested.DeclaringType : null;

    /// <summary>方法 IL 中的整数常量（及其 ±1、相反数 ±1）与类型操作数（isinst、newobj、box、newarr、ldtoken）。</summary>
    private static Hints HintsOf(Mono.Cecil.MethodDefinition method, CecilModel cecil)
    {
        var constants = new SortedSet<ulong>();
        var types = new List<TypeRef>();
        foreach (var instruction in method.Body.Instructions)
        {
            long? constant = instruction.OpCode.Code switch
            {
                Code.Ldc_I4_S => (sbyte)instruction.Operand, Code.Ldc_I4 => (int)instruction.Operand, Code.Ldc_I8 => (long)instruction.Operand,
                >= Code.Ldc_I4_M1 and <= Code.Ldc_I4_8 => instruction.OpCode.Code - Code.Ldc_I4_0,
                _ => null,
            };
            // 相反数也取：x == -3 常被写成 x + 3 == 0
            if (constant is { } c)
                foreach (var v in new[] { c - 1, c, c + 1, -c - 1, -c, -c + 1 }) constants.Add(unchecked((ulong)v));
            try
            {
                TypeRef? type = instruction.Operand switch
                {
                    Mono.Cecil.TypeReference t when instruction.OpCode.Code is Code.Isinst or Code.Box or Code.Ldtoken => cecil.Type(t),
                    Mono.Cecil.TypeReference t when instruction.OpCode.Code == Code.Newarr => new ArrayRef(cecil.Type(t), 1),
                    Mono.Cecil.MethodReference m when instruction.OpCode.Code == Code.Newobj => cecil.Method(m).DeclaringType,
                    _ => null,
                };
                if (type is not null && !types.Contains(type)) types.Add(type);
            }
            catch (Unsupported) { }
        }
        return new Hints(constants.ToArray(), types);
    }

    /// <summary>按 ABI 合成实参：this 为声明类型（或其具体子类）的对象，值类型的 this 为指向数据的指针；其余参数按类型取值。</summary>
    private static (List<byte[]> Bits, List<StackValue> Values) Arguments(World world, CilInterpreter interpreter, MethodRef method, Aapcs64Classifier.Signature signature)
    {
        var bits = new List<byte[]>();
        var values = new List<StackValue>();
        var types = StructAbi.ArgumentTypes(method);
        for (var position = 0; position < types.Length; position++)
        {
            var type = types[position];
            byte[] bytes;
            if (position == 0 && signature.This is not null)
            {
                var value = type is ByRefRef b ? world.ValueStorage(b.Element, "this") : world.Object(type, "this", 0);
                if (value == 0 && type is DefinitionRef { Definition: { IsInterface: false, IsValueType: false } } declared)
                    value = world.Instance(declared, "this", 0);
                if (value == 0) throw new Unsupported($"没有可作为 this 的 {type} 对象");
                bytes = StructAbi.Bytes(value, 8);
            }
            else bytes = world.ValueBytes(type, $"arg{position}");
            bits.Add(bytes);
            values.Add(interpreter.FromBytes(type, bytes));
        }
        return (bits, values);
    }

    /// <summary>方法清单（制表符分隔，第 addressColumn 列为十六进制入口、第 nameColumn 列为方法名，两者都要对得上）。</summary>
    private static RecoveryTarget[] ReadList(ProgramFacts facts, string path, int addressColumn, int nameColumn)
    {
        return File.ReadLines(path).Where(l => l.Length > 0 && !l.StartsWith('#')).Select(l => l.Split('\t')).Select(f =>
        {
            var address = Convert.ToUInt64(f[addressColumn], 16);
            return RecoveryTarget.Find(facts, address, f[nameColumn]);
        }).ToArray();
    }
}
