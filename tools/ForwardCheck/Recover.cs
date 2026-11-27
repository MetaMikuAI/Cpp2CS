using System.Text.Json;
using Cpp2CS.Discovery;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 恢复的主线（设计第 9、10 节）在语料上的运行与 IL 对照（第 15 节）：
/// 快照 → 效果图 → 发现 → 证明 → 选择 → 下降 → 托管方法体；恢复出的 IL 与真实 IL 都按目录展开，由同一个引擎证明等价。
/// 恢复过程只读快照、签名与全局事实，不读真实 IL；真实 IL 只用于对照。
/// </summary>
internal static partial class Recover
{
    /// <summary>
    /// isolated 为真时，整批跑完之后再把每个用例放进新的上下文（重新读入二进制、元数据、事实与快照）单独恢复一次，
    /// 与整批的结果逐例比较：结论不能依赖同一进程里先跑了哪些用例。
    /// </summary>
    public static int Run(string casesPath, string assemblies, string binary, string metadataPath, string? symbolFile, string target, string show,
        string? emit, string? generated, bool isolated = false, string? fingerprint = null)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(casesPath));
        var items = document.RootElement.EnumerateArray().ToList();
        var together = new Dictionary<string, string>(StringComparer.Ordinal);
        int status = Batch(items, assemblies, binary, metadataPath, symbolFile, target, show, emit, generated, fingerprint, together, quiet: false);
        if (!isolated) return status;
        var differences = new List<string>();
        int compared = 0;
        var clock = System.Diagnostics.Stopwatch.StartNew();
        foreach (var item in items)
        {
            var alone = new Dictionary<string, string>(StringComparer.Ordinal);
            Batch([item], assemblies, binary, metadataPath, symbolFile, target, "", null, null, fingerprint, alone, quiet: true);
            foreach (var (name, line) in alone)
            {
                compared++;
                if (!together.TryGetValue(name, out var batched) || batched != line) differences.Add($"{name}\n      整批：{batched?.Trim() ?? "没有"}\n      单独：{line.Trim()}");
            }
        }
        Console.WriteLine($"逐例单独恢复：用例 {compared} 个，与整批逐例相同 {compared - differences.Count} 个，不同 {differences.Count} 个；用时 {clock.Elapsed.TotalSeconds:F1} 秒");
        foreach (string line in differences) Console.WriteLine($"  不同  {line}");
        return status != 0 || differences.Count > 0 ? 1 : 0;
    }

    /// <summary>
    /// 恢复一组用例。summaries 按用例名记下每个用例的结论行（声明、凭据、选中的条数，等价与否，指令条数或各层的独立洞，首个洞）。
    /// quiet 为真时只做恢复与 IL 对照，不输出，不做对抗声明、交叉对照与写出。
    /// </summary>
    private static int Batch(IReadOnlyList<JsonElement> items, string assemblies, string binary, string metadataPath, string? symbolFile, string target,
        string show, string? emit, string? generated, string? fingerprint, Dictionary<string, string> summaries, bool quiet)
    {
        var input = Il2CppInput.Load(binary, metadataPath);
        byte[] bytes = File.ReadAllBytes(binary);
        using var metadata = ModelInput.Open(assemblies, input, bytes);
        var entities = new EntityFacts(metadata.Facts);
        var lifter = new Arm64Target(input.Elf, bytes,
            input.Code.Methods.Concat(input.Code.MethodInstances).Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        var facts = new BridgeFacts(input, metadata.Facts, symbolFile, bytes, lifter, fingerprint);
        if (!quiet && fingerprint != null) Console.WriteLine(facts.Admission);
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

        int cases = 0, equivalent = 0, different = 0, holed = 0, unreadable = 0, submitted = 0, certified = 0, chosen = 0, inexact = 0;
        var adversary = new Adversary();
        var output = emit == null && generated == null ? null : new Emit(emit ?? generated!, assemblies, metadata, facts);
        // 交叉对照的素材：已证明等价的用例的恢复结果，与签名相同的另一个用例的真实 IL 对照，应当被反驳。
        var recoveredBodies = new List<(string Name, string Signature, MethodBody Body, ITokenResolver Tokens)>();
        var realBodies = new List<(string Name, string Signature, MethodBody Body, ITokenResolver Tokens, TermPool Terms, int PointerBits)>();
        static string Signature(MethodShape shape) =>
            $"{shape.HasThis}({string.Join(",", shape.Parameters.Select(p => $"{p.Kind}/{p.StorageBits}/{p.Signed}/{p.TwoValued}"))})→{shape.Return?.Kind}/{shape.Return?.StorageBits}";
        var byReason = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var refuted = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var rows = new SortedDictionary<string, SortedSet<string>>(StringComparer.Ordinal);
        var assumed = new SortedDictionary<string, SortedSet<string>>(StringComparer.Ordinal);
        var lines = new List<string>();
        void Line(string name, string text)
        {
            lines.Add(text);
            summaries[name] = text;
        }
        var clock = System.Diagnostics.Stopwatch.StartNew();
        foreach (var item in items)
        {
            var description = item.GetProperty("case");
            var method = item.GetProperty("method");
            string name = $"{description.GetProperty("type").GetString()}::{description.GetProperty("method").GetString()}";
            bool shown = show.Length > 0 && (show == "all" || name.EndsWith("::" + show, StringComparison.Ordinal));
            var targets = item.GetProperty("mapping").GetProperty("targets");
            if (!targets.TryGetProperty(target, out var places) || places.GetArrayLength() == 0) continue;
            ulong address = Convert.ToUInt64(places[0].GetProperty("address").GetString()!, 16);
            var module = metadata.Load(Path.GetFileNameWithoutExtension(method.GetProperty("assembly").GetString()!));
            if (module is null) continue;
            cases++;
            MethodBody real;
            try
            {
                real = metadata.Body(module, Convert.ToInt32(method.GetProperty("token").GetString()!, 16));
            }
            catch (ExpansionException e)
            {
                unreadable++;
                Line(name, $"  不能对照 {name}：真实 IL 读不出来：{e.Message}");
                continue;
            }
            if (Snapshot(address) is not { } snapshot)
            {
                unreadable++;
                Line(name, $"  不能对照 {name}：没有快照");
                continue;
            }

            // 恢复：只读快照、签名与全局事实。
            var graph = new EffectGraph(snapshot, real.Method, facts, Snapshot);
            var view = new FactView(graph, entities, facts.Layout);
            var context = new RecoveryContext(snapshot, real.Method, real.InitializerOf, facts, entities, Snapshot);
            var claims = Propose(view).ToList();
            var (outcomes, explanation) = ProveAndSelect(view, context, claims);
            var body = Lowering.Lower(explanation);
            submitted += claims.Count;
            certified += outcomes.Count(o => o.Certificate is not null);
            chosen += explanation.Selected.Length;
            if (explanation.Inexact) inexact++;
            foreach (var outcome in outcomes)
            {
                foreach (string row in outcome.Certificate?.Rows ?? [])
                {
                    if (!rows.TryGetValue(row, out var users)) rows[row] = users = [];
                    users.Add(name);
                }
                foreach (string assumption in outcome.Certificate?.Assumptions ?? [])
                {
                    if (!assumed.TryGetValue(assumption, out var users)) assumed[assumption] = users = [];
                    users.Add(name);
                }
                if (outcome.Refutation is { } refutation) Tally(refuted, Reason(refutation.Layer.ToString(), refutation.Obligation));
            }
            if (shown)
            {
                Dump(name, graph);
                foreach (var outcome in outcomes)
                    Console.WriteLine($"  声明 {Text(outcome.Claim)}\n      {(outcome.Certificate is { } c
                        ? $"凭据：依赖 [{string.Join(", ", c.Before.Select(b => "B" + b.Index))}]，推后 [{string.Join(", ", c.After)}]，行 [{string.Join(", ", c.Rows)}]{(explanation.Selected.Contains(c) ? "  ← 选中" : "")}"
                        : $"反驳（{Reason(outcome.Refutation!.Layer.ToString(), outcome.Refutation.Obligation)}）：{outcome.Refutation.Detail}")}");
                Console.WriteLine($"  方法体（局部变量 {string.Join(", ", body.Locals.Select((l, i) => $"V_{i}: {l.Kind}"))}）");
                foreach (var instruction in body.Instructions)
                    Console.WriteLine(instruction.Opcode switch
                    {
                        ".label" => $"   L{instruction.Operand}:",
                        ".unrecovered" => $"      Unrecovered  // {body.Holes[(int)instruction.Operand].What}：{body.Holes[(int)instruction.Operand].Reason}",
                        _ => $"      {instruction.Opcode}{(instruction.Target >= 0 ? $" L{instruction.Target}" : instruction.Entity is { } entity ? $" {entity}" : instruction.Opcode is "ldarg" or "ldloc" or "stloc" or "ldc.i4" ? $" {instruction.Operand}" : "")}",
                    });
            }

            if (!body.Complete)
            {
                output?.CheckHoles(module, body);
                holed++;
                var kinds = new SortedDictionary<string, int>(StringComparer.Ordinal);
                foreach (var hole in body.Holes)
                {
                    if (hole.Derived) continue;
                    string reason = Reason(hole.Layer.ToString(), hole.Obligation);
                    Tally(byReason, reason);
                    Tally(kinds, reason);
                }
                var first = body.Holes.FirstOrDefault(h => !h.Derived) ?? body.Holes[0];
                Line(name, $"  有洞     {name}：声明 {claims.Count}、凭据 {outcomes.Count(o => o.Certificate is not null)}、选中 {explanation.Selected.Length}；"
                    + $"独立洞 {explanation.IndependentHoles}（{string.Join("，", kinds.Select(k => $"{k.Key} {k.Value}"))}）；首个：{first.What}：{Short(first.Reason)}");
                continue;
            }

            // IL 对照：恢复出的 IL 与真实 IL 都按目录展开，同一个引擎证明等价。
            var (recovered, tokens) = body.Encode()!.Value;
            string verdict;
            try
            {
                var expected = IlExpander.Expand(real, metadata.Facts, metadata.Tokens(module, real.Method.Entity), snapshot.Terms, 1, snapshot.PointerBits);
                var actual = IlExpander.Expand(recovered, entities, tokens, snapshot.Terms, 2, snapshot.PointerBits);
                var result = CoExecution.Equivalent(expected.Graph, actual.Graph, real, facts, metadata.Callees(snapshot.Terms, snapshot.PointerBits));
                verdict = result.Verdict == Verdict.Proved ? "" : $"{result.Verdict}：{result.Detail}";
            }
            catch (ExpansionException e)
            {
                verdict = $"不能展开：{e.Message}";
            }
            if (verdict.Length == 0) equivalent++;
            else different++;
            // 对抗声明：只在恢复结果已被真实 IL 证明等价的用例上做，参照是这份解释。
            if (verdict.Length == 0)
            {
                output?.Cases.Add(new(module, Convert.ToInt32(method.GetProperty("token").GetString()!, 16), name,
                    Signature(real.Method), body, real, snapshot.Terms, snapshot.PointerBits));
                recoveredBodies.Add((name, Signature(real.Method), recovered, tokens));
                realBodies.Add((name, Signature(real.Method), real, metadata.Tokens(module, real.Method.Entity), snapshot.Terms, snapshot.PointerBits));
            }
            if (verdict.Length == 0 && !quiet)
                adversary.Run(name, view, context, explanation, outcomes, candidate =>
                {
                    var (body2, tokens2) = candidate.Encode()!.Value;
                    var expected = IlExpander.Expand(real, metadata.Facts, metadata.Tokens(module, real.Method.Entity), snapshot.Terms, 1, snapshot.PointerBits);
                    var actual = IlExpander.Expand(body2, entities, tokens2, snapshot.Terms, 2, snapshot.PointerBits);
                    return CoExecution.Equivalent(expected.Graph, actual.Graph, real, facts, metadata.Callees(snapshot.Terms, snapshot.PointerBits)).Verdict == Verdict.Proved;
                });
            Line(name, $"  {(verdict.Length == 0 ? "等价    " : "不等价  ")} {name}：声明 {claims.Count}、凭据 {outcomes.Count(o => o.Certificate is not null)}、选中 {explanation.Selected.Length}"
                + $"、指令 {body.Instructions.Count(i => i.Opcode[0] != '.')} 条{(verdict.Length == 0 ? "" : "；" + Short(verdict))}");
        }

        if (quiet) return different == 0 ? 0 : 1;
        Console.WriteLine($"恢复与 IL 对照（{target}）：用例 {cases} 个，等价 {equivalent} 个，不等价 {different} 个，有洞 {holed} 个，不能对照 {unreadable} 个；用时 {clock.Elapsed.TotalSeconds:F1} 秒");
        Console.WriteLine($"  声明 {submitted} 条，凭据 {certified} 条，选中 {chosen} 条；选择不精确 {inexact} 个方法");
        Console.WriteLine($"  独立洞按层与义务：{string.Join("，", byReason.Select(k => $"{k.Key} {k.Value}"))}");
        Console.WriteLine($"  被反驳的声明按层与义务：{string.Join("，", refuted.Select(k => $"{k.Key} {k.Value}"))}");
        Console.WriteLine($"  用到的独立关系的行：{string.Join("，", rows.Select(r => $"{r.Key}（{r.Value.Count} 个用例）"))}");
        Console.WriteLine($"  凭据用到的有定义条件：{string.Join("，", assumed.Select(r => $"{r.Key}（{r.Value.Count} 个用例）"))}");
        foreach (string line in lines.Order(StringComparer.Ordinal)) Console.WriteLine(line);

        int pairs = 0, rejected = 0, number = 3;
        var passed = new List<string>();
        foreach (var expected in realBodies)
            foreach (var other in recoveredBodies)
            {
                if (other.Name == expected.Name || other.Signature != expected.Signature) continue;
                pairs++;
                var left = IlExpander.Expand(expected.Body, metadata.Facts, expected.Tokens, expected.Terms, number++, expected.PointerBits);
                var right = IlExpander.Expand(other.Body, entities, other.Tokens, expected.Terms, number++, expected.PointerBits);
                if (CoExecution.Equivalent(left.Graph, right.Graph, expected.Body, facts, metadata.Callees(expected.Terms, expected.PointerBits)).Verdict == Verdict.Proved) passed.Add($"{expected.Name} 的真实 IL ≡ {other.Name} 的恢复结果");
                else rejected++;
            }
        Console.WriteLine($"交叉对照：{pairs} 对（一个用例的真实 IL 配上签名相同的另一个用例的恢复结果），被反驳 {rejected} 对，被证明 {passed.Count} 对");
        foreach (string line in passed) Console.WriteLine($"  被证明：{line}");
        adversary.Report();
        bool emitted = emit == null || output!.Run(equivalent, pairs);
        if (generated != null) emitted &= output!.RunGenerated(generated, input, equivalent, pairs);
        return different == 0 && adversary.Failures == 0 && emitted ? 0 : 1;
    }

    private static readonly IDiscoverer[] Discoverers = [new GenericDiscoverer(), new GuardDiscoverer()];

    internal static IEnumerable<Claim> Propose(FactView view) =>
        Discoverers.SelectMany(d => d.Propose(view)).DistinctBy(c => c.Key);

    internal static (List<ProofOutcome> Outcomes, Explanation Explanation) ProveAndSelect(
        FactView view, RecoveryContext context, IEnumerable<Claim> claims)
    {
        var outcomes = claims.Select(c => Proof.Prove(context, c)).ToList();
        return (outcomes, Selection.Select(view, outcomes));
    }

    private static void Tally(SortedDictionary<string, int> counts, string key) => counts[key] = counts.GetValueOrDefault(key) + 1;

    internal static string Reason(string layer, Obligation? obligation) => (layer switch
    {
        "Fact" => "事实层",
        "Catalog" => "目录层",
        "Discovery" => "发现层",
        "Explanation" => "解释层",
        "Engine" => "引擎",
        "Budget" => "预算",
        "Selection" => "选择",
        "Value" => "值不可得",
        "Skeleton" => "骨架",
        _ => layer,
    }) + (obligation is { } o ? "/" + Refutation.Name(o) : "");

    private static string Short(string text) => text.Length <= 150 ? text : text[..150] + "…";

    private static string Text(Claim claim) =>
        $"{claim.Operation}{(claim.Entity is { } entity ? $" {entity}" : "")}（{string.Join("，", claim.Operands)}）占用 [{string.Join(", ", claim.Occupied)}] 落点 B{claim.Landing.Block.Index}.{claim.Landing.Index}"
        + (claim.Definition is { } definition ? $" 定义 {definition}" : "");

    private static void Dump(string name, EffectGraph graph)
    {
        Console.WriteLine($"== {name}{(graph.Failure is null ? "" : "  事实层：" + graph.Failure)}{(graph.Cyclic ? "  有环" : "")}");
        foreach (var (value, type, index) in graph.Arguments) Console.WriteLine($"  形参 {index}: {type.Kind}/{type.StorageBits} = {value}");
        foreach (int b in graph.Order)
        {
            var block = new BlockId(b);
            Console.WriteLine($"  B{b}{(graph.Tail(block) is var tail && tail != default ? $"  只抛出尾 {tail}" : "")}");
            for (int i = 0; i < graph.Snapshot.OccurrenceCount(block); i++)
                if (graph.Effect(new(block, i)) is { } e)
                    Console.WriteLine($"    {i}: {e.Kind} {e.Address}{(e.Kind == NativeEffectKind.Write ? " ← " + e.Value : "")}{(e.Width > 0 ? $"（{e.Width} 位）" : "")}"
                        + $"{(e.Callee is null ? "" : $" {e.Callee.Entity}({string.Join(", ", e.Arguments)}) → {e.Result}")}{e.Class}{(e.Exception != default ? " " + e.Exception : "")} {e.Detail}");
            if (graph.Condition(block) is { } condition) Console.WriteLine($"    条件 {condition}");
            if (graph.Returned(block) is { } returned) Console.WriteLine($"    返回 {returned}   槽 {graph.ReturnSlot(block)}");
        }
        foreach (var check in graph.Checks) Console.WriteLine($"  条件抛出 {EffectRef.Of(check.Edge)}: {check.Condition} = {check.Polarity} ⇒ {check.Exception}");
    }
}
