using System.Collections.Frozen;
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

public static class NoReturnAnalysis
{
    /// <summary>种子由装配处从系统目录提取，不能传入运行时符号核对的结果。</summary>
    public static NoReturnFacts Analyze(IImage image, IInstructionSet isa, RegisterConvention convention,
        IEnumerable<FunctionRange> ranges, IEnumerable<ImportSymbol> imports, IFlowFacts fallback)
    {
        var known = imports.Select(s => (CallTarget)new ImportedTarget(s)).ToHashSet();
        var functions = ranges.ToDictionary(r => r.Start);
        var dependents = new Dictionary<CallTarget, HashSet<ulong>>();
        var aliases = new Dictionary<CallTarget, CallTarget>();
        var pending = functions.Keys.ToHashSet();
        int rounds = 0;
        var extension = isa as INoReturnInstructionSet;
        while (pending.Count != 0)
        {
            rounds++;
            var added = new List<CallTarget>();
            foreach (var entry in pending.Order())
            {
                var target = new ImageFunction(entry);
                if (known.Contains(target)) continue;
                if (Prove(functions[entry])) added.Add(target);
            }
            pending.Clear();
            foreach (var target in added)
            {
                known.Add(target);
                if (dependents.TryGetValue(target, out var callers)) pending.UnionWith(callers);
            }
        }
        foreach (var (alias, target) in aliases) if (known.Contains(target)) known.Add(alias);
        return new(known, fallback, rounds);

        bool IsKnown(CallTarget target, ulong caller)
        {
            var resolved = extension?.ResolveCallTarget(image, target) ?? target;
            if (resolved != target) aliases[target] = resolved;
            if (!dependents.TryGetValue(resolved, out var callers)) dependents[resolved] = callers = [];
            callers.Add(caller);
            return known.Contains(resolved);
        }
        bool Prove(FunctionRange range)
        {
            // 已发现返回仍遍历其他路径，收集调用依赖及 PLT 别名，供整个映像提升使用。
            bool mayReturn = false;
            var visited = new HashSet<ulong>();
            var todo = new Stack<ulong>(); todo.Push(range.Start);
            bool Inside(ulong p) => p >= range.Start && p - range.Start < range.Length;
            while (todo.TryPop(out var pc))
            {
                if (!Inside(pc)) { if (!IsKnown(new ImageFunction(pc), range.Start)) mayReturn = true; continue; }
                if (!visited.Add(pc)) continue;
                var decoded = isa.Decode(pc);
                if (decoded.Instruction is not { Length: > 0 } instruction || (ulong)instruction.Length > range.Length - (pc - range.Start))
                { mayReturn = true; continue; }
                var facts = new ProbeFacts(t => IsKnown(t, range.Start));
                var emission = new Emission(pc, new TermTable(), isa.Registers, convention, facts);
                instruction.Emit(emission);
                if (emission.Failure is { } failure && extension?.IsStraightLineFailure(failure) != true)
                { mayReturn = true; continue; }
                switch (emission.End)
                {
                    case Finished { End: Unreachable }: break;
                    case Finished: case Indirect: mayReturn = true; break;
                    case null:
                        ulong next = pc + (ulong)instruction.Length;
                        if (next < pc || !Inside(next)) { mayReturn = true; break; }
                        todo.Push(next); break;
                    default:
                        foreach (var nextTarget in FunctionLifter.Targets(emission.End)) todo.Push(nextTarget);
                        break;
                }
            }
            return !mayReturn;
        }
    }
    private sealed class ProbeFacts(Func<CallTarget, bool> query) : IFlowFacts
    {
        public bool DoesNotReturn(CallTarget target) => query(target);
        public IndirectResolution ResolveIndirect(ulong address, Term target, IIndirectContext context)
            => new IndirectUnknown(new("noreturn.indirect", "不返回证明不解析间接跳转。"));
    }
}
