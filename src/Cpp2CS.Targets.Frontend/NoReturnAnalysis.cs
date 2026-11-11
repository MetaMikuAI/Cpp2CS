using System.Collections.Concurrent;
using System.Collections.Frozen;
using System.Diagnostics;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Targets.Frontend;

/// <summary>仅供不返回证明使用；不改变正常解码和提升。</summary>
public interface INoReturnInstructionSet
{
    bool IsStraightLineFailure(Reason reason);
    CallTarget ResolveCallTarget(IImage image, CallTarget target);
}

/// <summary>收敛后的不可变事实；间接跳转解析仍由原事实提供。</summary>
public sealed class NoReturnFacts : IFlowFacts
{
    internal NoReturnFacts(IEnumerable<CallTarget> targets, IFlowFacts fallback, int rounds)
    { Targets = targets.ToFrozenSet(); this.fallback = fallback; Rounds = rounds; }
    private readonly IFlowFacts fallback;
    public FrozenSet<CallTarget> Targets { get; }
    public int Rounds { get; }
    public bool DoesNotReturn(CallTarget target) => Targets.Contains(target);
    public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context)
        => fallback.ResolveIndirect(address, target, context);
}

/// <summary>可选的逐轮测量；探测时间按入口顺序排列，不参与分析判定。</summary>
public sealed record NoReturnRound(int Number, int Pending, int Added, TimeSpan Elapsed, IReadOnlyList<TimeSpan> Probes);

public static class NoReturnAnalysis
{
    private sealed record Dependency(CallTarget Target, bool Known, bool Stable);
    private sealed record ProbeNode(bool MayReturn, ulong[] Successors, Dependency[] Dependencies);
    private sealed class FunctionProbe(FunctionRange range)
    {
        internal FunctionRange Range { get; } = range;
        internal Dictionary<ulong, ProbeNode> Nodes { get; } = [];
        internal HashSet<CallTarget> Observed { get; } = [];
        internal List<(CallTarget Original, CallTarget Resolved)> NewDependencies { get; } = [];
        internal bool Proven { get; set; }
    }

    /// <summary>种子由装配处从系统目录提取，不能传入运行时符号核对的结果。并行时映像及指令集须可并发查询。</summary>
    public static NoReturnFacts Analyze(IImage image, IInstructionSet isa, RegisterConvention convention,
        IEnumerable<FunctionRange> ranges, IEnumerable<ImportSymbol> imports, IFlowFacts fallback,
        int jobs = 1, Action<NoReturnRound>? observe = null)
    {
        ArgumentOutOfRangeException.ThrowIfLessThan(jobs, 1);
        var known = imports.Select(s => (CallTarget)new ImportedTarget(s)).ToHashSet();
        var functions = ranges.ToDictionary(r => r.Start, r => new FunctionProbe(r));
        var dependents = new Dictionary<CallTarget, HashSet<ulong>>();
        var aliases = new Dictionary<CallTarget, CallTarget>();
        var resolutions = new ConcurrentDictionary<CallTarget, CallTarget>();
        var pending = functions.Keys.ToHashSet();
        int rounds = 0;
        var extension = isa as INoReturnInstructionSet;
        while (pending.Count != 0)
        {
            rounds++;
            var started = observe is null ? 0 : Stopwatch.GetTimestamp();
            var batch = pending.Order().Where(entry => !known.Contains(new ImageFunction(entry)))
                .Select(entry => functions[entry]).ToArray();
            var durations = observe is null ? null : new TimeSpan[batch.Length];
            // 已知集合在整轮内只读；每个函数独占缓存，依赖与别名在轮末按入口顺序合并。
            Parallel.For(0, batch.Length, new ParallelOptions { MaxDegreeOfParallelism = jobs }, i =>
            {
                var probeStart = observe is null ? 0 : Stopwatch.GetTimestamp();
                batch[i].Proven = Prove(batch[i]);
                if (durations is not null) durations[i] = Stopwatch.GetElapsedTime(probeStart);
            });
            var added = new List<CallTarget>();
            foreach (var function in batch)
            {
                foreach (var (original, resolved) in function.NewDependencies)
                {
                    if (resolved != original) aliases[original] = resolved;
                    if (!dependents.TryGetValue(resolved, out var callers)) dependents[resolved] = callers = [];
                    callers.Add(function.Range.Start);
                }
                function.NewDependencies.Clear();
                if (!function.Proven) continue;
                added.Add(new ImageFunction(function.Range.Start));
                function.Nodes.Clear();
            }
            observe?.Invoke(new(rounds, pending.Count, added.Count, Stopwatch.GetElapsedTime(started), durations!));
            pending.Clear();
            foreach (var target in added)
            {
                known.Add(target);
                if (dependents.TryGetValue(target, out var callers)) pending.UnionWith(callers);
            }
        }
        foreach (var (alias, target) in aliases) if (known.Contains(target)) known.Add(alias);
        return new(known, fallback, rounds);

        CallTarget Resolve(CallTarget target, FunctionProbe function)
        {
            // 计算目标含本条指令的项身份，不在全映像缓存中延长其项表的寿命。
            var resolved = extension is null ? target : target is ComputedTarget
                ? extension.ResolveCallTarget(image, target)
                : resolutions.GetOrAdd(target, t => extension.ResolveCallTarget(image, t));
            if (function.Observed.Add(target)) function.NewDependencies.Add((target, resolved));
            return resolved;
        }
        bool Unchanged(ProbeNode node)
        {
            foreach (var dependency in node.Dependencies)
                if (!dependency.Stable || known.Contains(dependency.Target) != dependency.Known) return false;
            return true;
        }
        bool Prove(FunctionProbe function)
        {
            var range = function.Range;
            // 已发现返回仍遍历其他路径，收集调用依赖及 PLT 别名，供整个映像提升使用。
            bool mayReturn = false;
            var visited = new HashSet<ulong>();
            var todo = new Stack<ulong>(); todo.Push(range.Start);
            bool Inside(ulong p) => p >= range.Start && p - range.Start < range.Length;
            while (todo.TryPop(out var pc))
            {
                if (!Inside(pc))
                { if (!known.Contains(Resolve(new ImageFunction(pc), function))) mayReturn = true; continue; }
                if (!visited.Add(pc)) continue;
                if (!function.Nodes.TryGetValue(pc, out var node)
                    || !Unchanged(node))
                    function.Nodes[pc] = node = Probe(pc);
                mayReturn |= node.MayReturn;
                foreach (var next in node.Successors) todo.Push(next);
            }
            return !mayReturn;

            ProbeNode Probe(ulong pc)
            {
                var decoded = isa.Decode(pc);
                if (decoded.Instruction is not { Length: > 0 } instruction || (ulong)instruction.Length > range.Length - (pc - range.Start))
                    return new(true, [], []);
                List<Dependency>? dependencies = null;
                var facts = new ProbeFacts(target =>
                {
                    var resolved = Resolve(target, function);
                    bool answer = known.Contains(resolved);
                    // 计算目标归一出的别名携带临时项身份，跨轮仍重新发射以保留别名收集行为。
                    (dependencies ??= []).Add(new(resolved, answer, target is not ComputedTarget || resolved == target));
                    return answer;
                });
                var emission = new Emission(pc, new TermTable(), isa.Registers, convention, facts);
                instruction.Emit(emission);
                var calls = dependencies?.ToArray() ?? [];
                // 只缓存控制流和已查询的答案，不保留发射出的语句或无关项。
                // 答案改变时仍走同一发射器，保持失败优先级及调用后的截断行为。
                if (emission.Failure is { } failure && extension?.IsStraightLineFailure(failure) != true)
                    return new(true, [], calls);
                switch (emission.End)
                {
                    case Finished { End: Unreachable }: return new(false, [], calls);
                    case Finished: case Indirect: return new(true, [], calls);
                    case null:
                        ulong next = pc + (ulong)instruction.Length;
                        return next < pc || !Inside(next) ? new(true, [], calls) : new(false, [next], calls);
                    default: return new(false, FunctionLifter.Targets(emission.End).ToArray(), calls);
                }
            }
        }
    }
    private sealed class ProbeFacts(Func<CallTarget, bool> query) : IFlowFacts
    {
        public bool DoesNotReturn(CallTarget target) => query(target);
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context)
            => new IndirectUnknown(new("noreturn.indirect", "不返回证明不解析间接跳转。"));
    }
}
