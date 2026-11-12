using Cpp2CS.Kernel.State;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>解码由装配处提供；可解码初值只在形状候选的使用处条件中作为证据。</summary>
public interface IRuntimeMetadataSlotValidator { bool IsValid(ulong imageOffset); }
/// <summary>每个直接调用点一项；提升失败或调用未进入 IR 时 Function、Call 为空，不能视为满足条件。</summary>
public sealed record RuntimeManagedUse(ulong Target, NativeFunction? Function, Call? Call);
/// <summary>按调用方延迟提升；消费完一项即可释放该方法的快照。</summary>
public sealed record RuntimeManagedCaller(ulong Entry, IReadOnlyDictionary<ulong, int> CallCounts, Func<IEnumerable<RuntimeManagedUse>> Read);
public sealed record RuntimeUsageCounts(int Satisfied, int Counterexamples, int Unverified, int Total)
{
    public int Checked => Satisfied + Counterexamples + Unverified;
    public bool Eligible => Counterexamples == 0 && Satisfied >= 16 && (long)Satisfied * 5 >= (long)Checked * 4;
}

/// <summary>按调用方入口排序取有界调用集，再并行消费快照；预算边界的调用方完整核对。</summary>
public sealed class RuntimeUsageEvidence(IImage image, MethodBinder binder, IRuntimeMetadataSlotValidator metadata,
    Func<IReadOnlySet<ulong>, IEnumerable<RuntimeManagedCaller>> callers, int jobs = 1)
{
    public const int CallLimit = 2000;
    private enum Verdict { Satisfied, Counterexample, Unverified }

    public IReadOnlyDictionary<ulong, RuntimeUsageCounts> Check(RuntimeFunction function, IReadOnlySet<ulong> candidates)
    {
        var counts = candidates.ToDictionary(e => e, _ => new RuntimeUsageCounts(0, 0, 0, 0));
        ArgumentOutOfRangeException.ThrowIfLessThan(jobs, 1);
        var signature = function.Signature is { } prototype ? binder.Classify(prototype).Value : null;
        var planned = candidates.ToDictionary(e => e, _ => 0);
        var selected = new List<(RuntimeManagedCaller Caller, IReadOnlySet<ulong> Targets)>();
        foreach (var caller in callers(candidates).OrderBy(c => c.Entry))
        {
            var targets = new HashSet<ulong>();
            foreach (var (target, count) in caller.CallCounts)
            {
                if (!candidates.Contains(target) || count <= 0) throw new InvalidOperationException("调用方索引含无效候选或调用点数。");
                counts[target] = counts[target] with { Total = counts[target].Total + count };
                if (planned[target] >= CallLimit) continue;
                planned[target] += count;
                targets.Add(target);
            }
            if (targets.Count > 0) selected.Add((caller, targets));
        }
        Parallel.ForEach(selected, new ParallelOptions { MaxDegreeOfParallelism = jobs }, item =>
        {
            var local = item.Targets.ToDictionary(e => e, _ => new RuntimeUsageCounts(0, 0, 0, 0));
            var state = new StateQueries(image: image);
            NativeFunction? previous = null;
            QueryContext? context = null;
            foreach (var use in item.Caller.Read())
            {
                if (!candidates.Contains(use.Target)) throw new InvalidOperationException("使用处来源返回了候选集合之外的调用。");
                if (!item.Targets.Contains(use.Target)) continue;
                var verdict = Verdict.Unverified;
                if (signature is not null && use.Function is { } body && use.Call is { } call)
                {
                    if (!ReferenceEquals(previous, body)) { previous = body; context = state.CreateContext(body); }
                    var bound = binder.Call(call, signature, body.Terms).Value;
                    if (bound is not null)
                    {
                        verdict = Verdict.Satisfied;
                        foreach (var condition in function.Recognition.UsageConditions)
                        {
                            var value = bound.Arguments[condition.Parameter].Source is TermSource source
                                ? CheckArgument(source.Term, condition, state, context!) : Verdict.Unverified;
                            if (value == Verdict.Counterexample) { verdict = value; break; }
                            if (value == Verdict.Unverified) verdict = value;
                        }
                    }
                }
                var count = local[use.Target];
                local[use.Target] = verdict switch
                {
                    Verdict.Satisfied => count with { Satisfied = count.Satisfied + 1 },
                    Verdict.Counterexample => count with { Counterexamples = count.Counterexamples + 1 },
                    _ => count with { Unverified = count.Unverified + 1 }
                };
            }
            lock (counts)
                foreach (var (entry, count) in local)
                {
                    if (count.Checked != item.Caller.CallCounts[entry]) throw new InvalidOperationException("调用点数与调用方索引不一致。");
                    var prior = counts[entry];
                    counts[entry] = new(prior.Satisfied + count.Satisfied, prior.Counterexamples + count.Counterexamples,
                        prior.Unverified + count.Unverified, prior.Total);
                }
        });
        return counts;
    }

    private Verdict CheckArgument(Term argument, RuntimeUsageCondition condition, StateQueries state, QueryContext context)
    {
        var pending = new Stack<(Term Value, bool Leaving)>(); pending.Push((argument, false));
        var active = new HashSet<Term>(); var done = new HashSet<Term>();
        bool invalid = false, opaque = false; int constants = 0;
        while (pending.TryPop(out var item))
        {
            if (item.Leaving) { active.Remove(item.Value); done.Add(item.Value); continue; }
            var resolved = context.Get(state.Resolve, item.Value);
            if (!resolved.IsSuccess) { opaque = true; continue; }
            var value = resolved.Value;
            if (done.Contains(value)) continue;
            if (!active.Add(value)) { opaque = true; continue; }
            pending.Push((value, true));
            IEnumerable<Term>? sources = null;
            if (value.Operator is CoreOperator { Operation: CoreOperation.Select }) sources = value.Operands.Skip(1);
            else if (value.Identity is ResultAtom { Definition: MergeIdentity id })
                sources = context.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs.Select(i => i.Value);
            else if (value.Identity is MemoryMerge merge)
            {
                var inputs = context.Get(state.MergeInputs, merge);
                if (!inputs.IsSuccess) { opaque = true; continue; }
                sources = inputs.Value.Select(i => i.Value);
            }
            if (sources is not null)
            {
                var inputs = sources.ToArray();
                if (inputs.Length == 0) opaque = true;
                foreach (var source in inputs) pending.Push((source, false));
                continue;
            }
            var location = context.Get(state.Locations, new(value, image.PointerWidth * 8));
            if (location.IsSuccess && location.Value is { Region: Region.Image, Offset: { } offset })
            {
                constants++;
                if (offset < 0 || offset > ulong.MaxValue) { invalid = true; continue; }
                var address = (ulong)offset;
                var info = image.Query(address);
                invalid |= info.Executable || info.Storage != StorageKind.FileContent || info.AvailableBytes < (ulong)image.PointerWidth
                    || condition.Kind != RuntimeUsageConditionKind.MetadataSlotAddress
                    || !image.IsWritable(address, (ulong)image.PointerWidth) || !metadata.IsValid(address);
            }
            else if (value.ConstantValue is not null) { constants++; invalid = true; }
            else opaque = true;
        }
        return opaque || constants == 0 ? Verdict.Unverified : invalid ? Verdict.Counterexample : Verdict.Satisfied;
    }
}
