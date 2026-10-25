using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Lifting;

namespace Cpp2CS.Idioms;

/// <summary>按类别累计的计数与少量样例。</summary>
public sealed class Tally
{
    public const int SampleLimit = 5;
    public long Count;
    public List<string> Samples { get; } = [];

    public void Add(string sample, long count = 1)
    {
        Count += count;
        if (Samples.Count < SampleLimit) Samples.Add(sample);
    }

    public void Merge(Tally other)
    {
        Count += other.Count;
        foreach (var s in other.Samples)
            if (Samples.Count < SampleLimit) Samples.Add(s);
    }
}

/// <summary>
/// L2 模板普查：对一组函数做提升与惯用法归一，汇总模板命中、改写前的 helper 调用点、残余与错误。
/// 覆盖率口径：一个调用点在改写之后不再是"没有 Op 的 helper 调用"，即视为被模板消化（含守卫整体删除的调用）。
/// </summary>
public sealed class IdiomCensus
{
    public int Functions { get; private set; }
    public int Failed { get; private set; }
    /// <summary>没有任何残余与错误的函数数。</summary>
    public int Clean { get; private set; }
    public Dictionary<Template, long> Hits { get; } = new();
    public Dictionary<HelperKind, long> HelperCalls { get; } = new();
    public long IndirectCalls { get; private set; }
    public Dictionary<string, Tally> Residuals { get; } = new();
    public Dictionary<string, Tally> Errors { get; } = new();
    /// <summary>调用约定见证（不计入残余）：见 <see cref="AbiChecks"/>。</summary>
    public Dictionary<string, Tally> Abi { get; } = new();
    /// <summary>守卫字节 → 把它当作守卫的函数（入口）。</summary>
    public Dictionary<ulong, List<ulong>> GuardOwners { get; } = new();
    /// <summary>守卫字节 → 各处初始化的不同槽位集合（以逗号连接的十六进制地址）。同一字节属于同一个方法（内联会把它带进调用方），集合应当只有一种。</summary>
    public Dictionary<ulong, HashSet<string>> GuardSlotSets { get; } = new();
    public TimeSpan Elapsed { get; private set; }
    /// <summary>
    /// 每个模板保留 <see cref="InstanceLimit"/> 个实例（供 Unicorn 等价性测试）：按（函数, 起点）的散列取最小的若干个，
    /// 即在全部实例上均匀、确定地抽样，与并行划分无关。
    /// </summary>
    public Dictionary<Template, List<TemplateInstance>> Instances { get; } = new();
    public const int InstanceLimit = 400;

    private static ulong SampleKey(TemplateInstance instance)
    {
        var x = instance.Function * 0x9E3779B97F4A7C15UL ^ instance.Head;
        x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9UL;
        x = (x ^ (x >> 27)) * 0x94D049BB133111EBUL;
        return x ^ (x >> 31);
    }

    private static void Keep(Dictionary<Template, List<TemplateInstance>> instances, Template template, IEnumerable<TemplateInstance> add)
    {
        if (!instances.TryGetValue(template, out var list)) instances[template] = list = [];
        list.AddRange(add);
        if (list.Count < 2 * InstanceLimit) return;
        list.Sort((a, b) => SampleKey(a).CompareTo(SampleKey(b)));
        list.RemoveRange(InstanceLimit, list.Count - InstanceLimit);
    }

    /// <summary>某类 helper 的残余调用点数（类别形如 helper:Kind 或 helper:Kind(detail)）。</summary>
    public long ResidualCalls(HelperKind kind) => Residuals
        .Where(p => p.Key.StartsWith("helper:") && p.Key[7..].Split('(')[0] == kind.ToString()).Sum(p => p.Value.Count);

    public static IdiomCensus Run(ProgramFacts facts, IReadOnlyList<CodeFunction> functions, Action<string>? log = null)
    {
        var census = new IdiomCensus();
        var started = DateTime.UtcNow;
        var gate = new object();
        var done = 0;
        // 函数很多时按入口散列抽 1/8 的函数记录模板实例（每个模板最终只保留 InstanceLimit 个）
        Func<ulong, bool>? recordFilter = functions.Count > 50_000 ? entry => (entry * 0x9E3779B97F4A7C15UL >> 61) == 0 : null;
        var lifters = new ThreadLocal<(FunctionLifter, IdiomRewriter)>(() => (new FunctionLifter(facts), new IdiomRewriter(facts) { RecordFilter = recordFilter }));
        var entryReads = new System.Collections.Concurrent.ConcurrentDictionary<ulong, int>();
        var unset = new System.Collections.Concurrent.ConcurrentBag<(ulong Callee, int Bit, string Sample)>();
        Parallel.ForEach(System.Collections.Concurrent.Partitioner.Create(0, functions.Count, 500), range =>
        {
            var local = new IdiomCensus();
            var (lifter, rewriter) = lifters.Value;
            for (var i = range.Item1; i < range.Item2; i++)
            {
                var function = functions[i];
                var name = $"0x{function.Start:x} {facts.EntriesAt(function.Start).FirstOrDefault()?.Method?.ToString() ?? "?"}";
                local.Functions++;
                try
                {
                    var lifted = lifter.Lift(function.Start);
                    if (!lifted.Succeeded)
                    {
                        local.Failed++;
                        Add(local.Errors, "ssa:" + Category(lifted.Errors[0]), $"{name}: {lifted.Errors[0]}");
                        continue;
                    }
                    if (lifter.Calls is FactsCallModel model) entryReads[function.Start] = AbiChecks(model, lifted.Function, name, local.Abi, unset);
                    var result = rewriter.Run(lifted.Function);
                    foreach (var (template, count) in result.Hits) local.Hits[template] = local.Hits.GetValueOrDefault(template) + count;
                    foreach (var (kind, count) in result.HelperCalls) local.HelperCalls[kind] = local.HelperCalls.GetValueOrDefault(kind) + count;
                    local.IndirectCalls += result.IndirectCalls;
                    foreach (var residual in result.Residuals) Add(local.Residuals, residual.Category, $"{name} @0x{residual.Address:x}: {residual.Detail}");
                    foreach (var error in result.Errors.Take(1)) Add(local.Errors, "rewrite:" + Category(error), $"{name}: {error}");
                    foreach (var (guard, slots) in result.GuardSlots)
                    {
                        if (!local.GuardOwners.TryGetValue(guard, out var owners)) local.GuardOwners[guard] = owners = [];
                        owners.Add(function.Start);
                        if (!local.GuardSlotSets.TryGetValue(guard, out var sets)) local.GuardSlotSets[guard] = sets = [];
                        sets.Add(string.Join(",", slots.Select(x => x.ToString("x"))));
                    }
                    foreach (var instance in result.Instances) Keep(local.Instances, instance.Template, [instance]);
                    if (result.Errors.Count > 0) local.Failed++;
                    else if (result.Residuals.Count == 0) local.Clean++;
                }
                catch (Exception e)
                {
                    local.Failed++;
                    Add(local.Errors, "exception:" + e.GetType().Name, $"{name}: {e.Message} {e.StackTrace?.Split('\n').FirstOrDefault()?.Trim()}");
                }
            }
            lock (gate)
            {
                census.Merge(local);
                done += range.Item2 - range.Item1;
                if (log is not null && done / 50000 != (done - (range.Item2 - range.Item1)) / 50000)
                    log($"  {done}/{functions.Count} 函数，{(DateTime.UtcNow - started).TotalSeconds:F0} s");
            }
        });
        // 调用方没有设置的参数寄存器（值为被调用破坏的未定义值）：被调用者入口确实不读它时，是编译器对无用参数的省略
        foreach (var (callee, bit, sample) in unset)
        {
            var key = !entryReads.TryGetValue(callee, out var mask) ? "abi:unset-argument:callee-not-lifted"
                : (mask & (1 << bit)) == 0 ? "abi:unset-argument:unused-by-callee" : "abi:unset-argument:READ-by-callee";
            Add(census.Abi, key, sample);
        }
        foreach (var list in census.Instances.Values)
        {
            list.Sort((a, b) => SampleKey(a).CompareTo(SampleKey(b)));
            if (list.Count > InstanceLimit) list.RemoveRange(InstanceLimit, list.Count - InstanceLimit);
        }
        census.Elapsed = DateTime.UtcNow - started;
        return census;
    }

    private static readonly Storage[] ArgumentRegisters = [.. Enumerable.Range(0, 9).Select(Storage.Gpr), .. Enumerable.Range(0, 8).Select(Storage.Vec)];

    /// <summary>
    /// 调用约定的见证：函数体读取的入口参数寄存器应在自身签名之内；被调用破坏的寄存器不应再被使用。
    /// 只看非调用语句与按签名确定参数的调用（保守约定的调用会读取全部参数寄存器，不能作为见证）。
    /// </summary>
    private static int AbiChecks(FactsCallModel model, Flow.MachineFunction function, string name, Dictionary<string, Tally> residuals,
        System.Collections.Concurrent.ConcurrentBag<(ulong, int, string)> unset)
    {
        var own = model.Signature(function.Entry);
        var reads = 0;
        foreach (var stmt in function.Blocks.SelectMany(b => b.Statements))
        {
            CallSignature? callee = null;
            if (stmt is Call call && !(call is { Kind: CallKind.Direct or CallKind.Tail, Target: Const t } && (callee = model.Signature(t.Value)) is not null)) continue;
            var operands = ExprMap.Operands(stmt).ToList();
            for (var k = 0; k < operands.Count; k++)
            {
                // 调用的第 k 个参数（Operands 第 0 项是调用目标）对应的寄存器；是被调用者的 MethodInfo* 参数时单独计
                var methodInfo = stmt is Call c && k > 0 && k - 1 < c.Sources.Length && c.Sources[k - 1] == callee?.MethodInfo;
                foreach (var e in ExprMap.Walk(operands[k]))
                {
                    if (e is Use { Variable: { Version: 0 } r } && Array.IndexOf(ArgumentRegisters, r.Storage) is var bit and >= 0) reads |= 1 << bit;
                    if (own is not null && e is Use { Variable: { Version: 0 } v } && ArgumentRegisters.Contains(v.Storage) && !own.Reads.Contains(v.Storage))
                        Add(residuals, methodInfo ? "abi:methodinfo-passthrough" : $"abi:entry-read-beyond-signature:{v.Storage}", $"{name} @0x{stmt.Address:x}: {Clip(stmt)}");
                    else if (e is Unknown { Reason: var reason } && reason.EndsWith("被调用破坏"))
                    {
                        if (methodInfo) Add(residuals, "abi:methodinfo-unset", $"{name} @0x{stmt.Address:x}: {Clip(stmt)}");
                        else if (stmt is Call { Target: Const target } unsetCall && k > 0 && k - 1 < unsetCall.Sources.Length && Array.IndexOf(ArgumentRegisters, unsetCall.Sources[k - 1]) is var argBit and >= 0)
                            unset.Add((target.Value, argBit, $"{name} @0x{stmt.Address:x}: {Clip(stmt)}"));
                        else Add(residuals, $"abi:use-of-clobbered:{stmt.GetType().Name}", $"{name} @0x{stmt.Address:x}: {Clip(stmt)}");
                    }
                }
            }
        }
        return reads;
    }

    private static string Clip(Stmt stmt) => stmt.ToString() is var s && s.Length > 240 ? s[..240] : s;

    /// <summary>错误文本的类别：去掉地址与变量名，只留描述。</summary>
    private static string Category(string error) =>
        System.Text.RegularExpressions.Regex.Replace(error, @"0x[0-9a-f]+|[a-z]+\d+_-?\d+|in_[a-z]+\d+|B\d+@\S+", "_").Trim();

    private static void Add(Dictionary<string, Tally> tallies, string key, string sample)
    {
        if (!tallies.TryGetValue(key, out var tally)) tallies[key] = tally = new Tally();
        tally.Add(sample);
    }

    private void Merge(IdiomCensus other)
    {
        Functions += other.Functions;
        Failed += other.Failed;
        Clean += other.Clean;
        IndirectCalls += other.IndirectCalls;
        foreach (var (k, v) in other.Hits) Hits[k] = Hits.GetValueOrDefault(k) + v;
        foreach (var (k, v) in other.HelperCalls) HelperCalls[k] = HelperCalls.GetValueOrDefault(k) + v;
        foreach (var (k, v) in other.GuardSlotSets)
        {
            if (!GuardSlotSets.TryGetValue(k, out var sets)) GuardSlotSets[k] = sets = [];
            sets.UnionWith(v);
        }
        foreach (var (k, v) in other.GuardOwners)
        {
            if (!GuardOwners.TryGetValue(k, out var owners)) GuardOwners[k] = owners = [];
            owners.AddRange(v);
        }
        foreach (var (k, v) in other.Residuals)
        {
            if (!Residuals.TryGetValue(k, out var t)) Residuals[k] = t = new Tally();
            t.Merge(v);
        }
        foreach (var (k, v) in other.Errors)
        {
            if (!Errors.TryGetValue(k, out var t)) Errors[k] = t = new Tally();
            t.Merge(v);
        }
        foreach (var (k, v) in other.Instances) Keep(Instances, k, v);
        foreach (var (k, v) in other.Abi)
        {
            if (!Abi.TryGetValue(k, out var t)) Abi[k] = t = new Tally();
            t.Merge(v);
        }
    }
}
