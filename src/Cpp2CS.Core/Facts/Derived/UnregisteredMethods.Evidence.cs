using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Lifting;
using static Cpp2CS.Facts.UnregisteredMethods;

namespace Cpp2CS.Facts.Derived;

public static partial class UnregisteredInference
{
    private sealed class Observation(ulong caller, CodeRef reference)
    {
        public ulong Caller { get; } = caller;
        public CodeRef Reference { get; } = reference;
        public bool Failed { get; set; }
        public Dictionary<Storage, MethodRef[]> Symbols { get; } = [];
        public List<MethodRef> Positive { get; } = [];
    }

    public static UnregisteredMethods Build(BaseFacts facts, Action<string>? log = null)
    {
        return new Builder(facts, log).Run();
    }

    private sealed partial class Builder(BaseFacts facts, Action<string>? log)
    {
        private readonly ManagedAbi abi = new(facts.Layouts);
        private readonly Dictionary<MethodRef, AbiSignature?> signatures = [];
        private readonly Dictionary<ulong, HashSet<ulong>> guards = [];
        private readonly Dictionary<ulong, HashSet<ulong>> guardBranches = [];
        private readonly Dictionary<ulong, bool> addressProofs = [];
        private readonly List<string> analysisErrors = [];
        private AbiSignature? Signature(MethodRef method)
        {
            // 开放参数的相等性只包含名称和槽位，不包含调用者的约束；不能跨调用者复用分类。
            if (!IsClosed(method)) return ClassifyInstance(method, abi);
            if (!signatures.TryGetValue(method, out var result)) signatures[method] = result = ClassifyInstance(method, abi);
            return result;
        }

        public UnregisteredMethods Run()
        {
            var result = new UnregisteredMethods();
            var functions = facts.Code.Functions.Where(f => f.Region == CodeRegion.Managed && facts.EntriesAt(f.Start).Length == 0).ToDictionary(f => f.Start);
            var sites = facts.Scan.All.Where(r => r.Kind is RefKind.Call or RefKind.TailCall && functions.ContainsKey(r.Target))
                .Select(r => new Observation(facts.Code.At(r.Site)!.Start, r)).ToArray();
            Observe(sites);
            // 整个注册集合参与歧义否决；不能先按 A 的定义过滤再宣布 B 唯一。
            var shapes = RegisteredShapes();
            var conflicts = new List<string>();
            var abiProblems = new List<string>();
            var contradictions = new List<string>();
            foreach (var group in sites.GroupBy(s => s.Reference.Target).OrderBy(g => g.Key))
            {
                var observations = group.ToArray();
                var positive = observations.SelectMany(s => s.Positive).Distinct().ToArray();
                var complete = positive.Where(IsComplete).ToArray();
                var definitions = positive.Select(m => m.Method).Distinct().ToArray();
                var definition = definitions.Length == 1 ? definitions[0] : null;
                var reason = "A/无见证";
                AbiSignature? signature = null;
                ulong[] matches = [];
                var adjustors = Adjustors(group.Key, observations);
                if (definitions.Length > 1) reason = "A/不同定义冲突";
                else if (definition is not null && complete.Length == 0) reason = "A/不完整实例";
                else if (definition is not null)
                {
                    signature = Signature(complete[0])!;
                    var register = signature.MethodInfo!.Register;
                    reason = observations.Any(s => s.Symbols.TryGetValue(register, out var symbols) && symbols.Any(m => m.Method != definition)) ? "A/不同定义冲突"
                        : observations.Any(s => s.Failed) ? "A/分析不完整"
                        : complete.Any(m => Signature(m) is not { } sig || Shape(sig) != Shape(signature)) ? "ABI/正见证不吻合"
                        : "A/通过";
                    // 非单值符号也不能掩盖 ABI 冲突；它不给正见证，但有否决权。
                    if (reason == "A/通过" && observations.SelectMany(s => s.Symbols.GetValueOrDefault(register) ?? [])
                        .Where(IsComplete).Any(m => Signature(m) is { } sig && Shape(sig) != Shape(signature))) reason = "ABI/候选槽位不吻合";
                    if (reason == "A/通过")
                    {
                        reason = Compare(functions[group.Key], definition, signature, shapes, out matches);
                        // ABI 由本调用的完整实例分类；开放参数不替换成任意封闭见证。
                    }
                }
                if (reason == "A/不同定义冲突") conflicts.Add($"0x{group.Key:x}: {string.Join(';', positive.Select(m => m.ToString()))}");
                if (reason.StartsWith("ABI/", StringComparison.Ordinal)) abiProblems.Add($"0x{group.Key:x}: {reason}");
                if (definition is not null && adjustors.Any(e => e.Method!.Method != definition))
                {
                    reason = "注册调整器/定义矛盾";
                    contradictions.Add($"0x{group.Key:x}: A={definition.Index}, adjustors={string.Join(';', adjustors.Select(e => e.ToString()))}");
                }
                if (reason == "接受")
                    result.accepted.Add(group.Key, new(group.Key, definition!, signature!,
                        observations.SelectMany(s => s.Positive.Where(IsComplete).Select(m => new MethodWitness(s.Caller, s.Reference.Site, m))).ToArray(), matches, adjustors));
                result.decisions.Add(new(group.Key, reason, observations.Length, observations.Count(s => s.Positive.Count > 0), positive.Length, definition?.Index));
            }
            facts.Checks.Add("unregistered.definition-conflict", "Warning", functions.Count, conflicts, "不同定义的 MethodInfo 见证，拒绝身份推断");
            facts.Checks.Add("unregistered.abi", "Warning", functions.Count, abiProblems, "正见证或注册同形体 ABI 不吻合，拒绝身份推断");
            facts.Checks.Add("unregistered.analysis", "Warning", sites.Length, analysisErrors, "调用者提升/L2 不完整，相关目标不接受");
            facts.Checks.Add("unregistered.registration", "Error", functions.Count, contradictions, "A 与注册调整器精确跳转的定义矛盾");
            facts.Checks.Info("unregistered.definitions", result.All.Count, string.Join("；", result.Decisions.GroupBy(d => d.Reason).OrderBy(g => g.Key).Select(g => $"{g.Key}={g.Count()}")));
            log?.Invoke($"未注册定义：{result.All.Count}/{functions.Count}；原始调用点 {sites.Length}");
            return result;
        }

        private CodeEntry[] Adjustors(ulong target, Observation[] sites) => sites.Select(s => s.Caller).Distinct()
            .Where(entry => facts.Code.At(entry) is { Size: 8 } && facts.Code.Word(entry) == 0x91004000
                && facts.Code.Word(entry + 4) is { } jump && A64.IsB(jump) && A64.Imm26Target(jump, entry + 4) == target)
            .SelectMany(facts.EntriesAt).Where(e => e.Method is not null && e.Kind is EntryKind.AdjustorThunk or EntryKind.GenericAdjustorThunk).ToArray();

        private void Observe(Observation[] sites)
        {
            var lifter = new FunctionLifter(facts);
            var rewriter = new IdiomRewriter(facts) { RecordFilter = _ => false };
            foreach (var group in sites.GroupBy(s => s.Caller))
            {
                var lifted = lifter.Lift(group.Key);
                var rewritten = lifted.Succeeded ? rewriter.Run(lifted.Function) : null;
                if (!lifted.Succeeded || rewritten!.Errors.Count > 0)
                {
                    foreach (var site in group) site.Failed = true;
                    analysisErrors.Add($"0x{group.Key:x}: {string.Join(';', lifted.Errors.Concat(rewritten?.Errors ?? []))}");
                    continue;
                }
                guards[group.Key] = rewritten.Guards;
                guardBranches[group.Key] = rewritten.MetadataGuardBranches;
                var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
                var definitions = statements.OfType<Define>().Concat(lifted.Function.Dead.Select(d => d.Define))
                    .GroupBy(d => d.Target).ToDictionary(g => g.Key, g => g.First().Value);
                var phis = statements.OfType<Phi>().ToDictionary(p => p.Target);
                var calls = statements.OfType<Call>().ToLookup(c => c.Address);
                foreach (var site in group)
                {
                    var call = calls[site.Reference.Site].SingleOrDefault(c => c.Target is Const target && target.Value == site.Reference.Target);
                    if (call is null) continue;
                    for (var i = 0; i < call.Arguments.Length; i++)
                    {
                        var storage = call.Sources[i];
                        var symbols = Methods(call.Arguments[i], definitions, phis, []);
                        if (symbols.Length == 0) continue;
                        site.Symbols[storage] = symbols;
                        if (Expand(call.Arguments[i], definitions, []) is Symbol { Kind: SymbolKind.Method, Value: MethodRef method }
                            && Signature(method)?.MethodInfo?.Register == storage) site.Positive.Add(method);
                    }
                }
            }
            log?.Invoke($"未注册定义 A 普查完成：{sites.Select(s => s.Caller).Distinct().Count()} 调用者");
        }

        private static Expr Expand(Expr value, Dictionary<Variable, Expr> definitions, HashSet<Variable> path) =>
            value is Use { Width: 64 } use && definitions.TryGetValue(use.Variable, out var next) && path.Add(use.Variable) ? Expand(next, definitions, path) : value;

        private static MethodRef[] Methods(Expr value, Dictionary<Variable, Expr> definitions, Dictionary<Variable, Phi> phis, HashSet<Variable> path)
        {
            if (value is Symbol { Kind: SymbolKind.Method, Value: MethodRef method }) return [method];
            if (value is Select select) return Methods(select.True, definitions, phis, new(path)).Concat(Methods(select.False, definitions, phis, new(path))).Distinct().ToArray();
            if (value is not Use { Width: 64 } use || !path.Add(use.Variable)) return [];
            if (definitions.TryGetValue(use.Variable, out var next)) return Methods(next, definitions, phis, path);
            return phis.TryGetValue(use.Variable, out var phi) ? phi.Sources.SelectMany(v => Methods(new Use(v, 64), definitions, phis, new(path))).Distinct().ToArray() : [];
        }
    }
}
