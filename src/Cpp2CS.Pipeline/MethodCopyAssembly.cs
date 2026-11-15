using System.Collections.Concurrent;
using System.Collections.Immutable;
using System.Diagnostics;
using System.Reflection;
using Cpp2CS.Input;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.MethodCopies;
using Cpp2CS.Recovery.Inlining;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Pipeline;

public sealed record MethodCopyAttempt(ulong RegisteredEntry, MethodRef Method, Reason? Failure, int Matched);

public sealed class MethodCopySurvey
{
    public const int CandidateLimit = 64;
    public MethodCopyFacts Facts { get; internal set; } = MethodCopyFacts.Empty;
    public ImmutableDictionary<ulong, ImmutableArray<ulong>> Callers { get; internal set; } = ImmutableDictionary<ulong, ImmutableArray<ulong>>.Empty;
    internal ConcurrentDictionary<ulong, Reason> Reasons { get; } = [];
    internal ConcurrentDictionary<ulong, int> Counts { get; } = [];
    internal ConcurrentDictionary<ulong, ImmutableArray<MethodCopyAttempt>> Attempts { get; } = [];
    public ImmutableDictionary<ulong, Reason> Missing => Reasons.ToImmutableDictionary();
    public ImmutableDictionary<ulong, int> CandidateCounts => Counts.ToImmutableDictionary();
    public int CappedTargets => Counts.Count(p => p.Value > CandidateLimit);
    internal long Ticks, FrontendTicks, RecoveryTicks, CompareTicks;
    internal int Targets, Registered;
    public int LiftedTargets => Targets;
    public int LiftedRegistered => Registered;
    public double Seconds => (double)Interlocked.Read(ref Ticks) / Stopwatch.Frequency;
    internal ImmutableDictionary<string, double> InitialTimings { get; set; } = ImmutableDictionary<string, double>.Empty;
    public ImmutableDictionary<string, double> Timings => InitialTimings
        .SetItem("按需提升", (double)Interlocked.Read(ref FrontendTicks) / Stopwatch.Frequency)
        .SetItem("候选管线（含前端和依赖）", (double)Interlocked.Read(ref RecoveryTicks) / Stopwatch.Frequency)
        .SetItem("同构核对", (double)Interlocked.Read(ref CompareTicks) / Stopwatch.Frequency);
}

/// <summary>按运行普查并建索引，按需用候选身份恢复两侧；只有完整托管体同构才能提供身份。</summary>
public static class MethodCopyAssembly
{
    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<GlobalFacts, Lazy<MethodCopySurvey>> values = [];
    public static MethodCopySurvey Get(GlobalFacts facts) => values.GetValue(facts, f => new(() => Build(f))).Value;
    public static double Seconds(GlobalFacts facts) => values.TryGetValue(facts, out var value) && value.IsValueCreated ? value.Value.Seconds : 0;
    public static bool Aggressive(MethodDef method) => (method.ImplAttributes & MethodImplAttributes.AggressiveInlining) != 0;
    // 无 IL 的元数据只能给出访问器的签名上界；恢复注册体后再核对单字段模板。
    public static bool EligibleCandidate(MethodDef method) => method.DeclaresCilBody && (method.ImplAttributes & MethodImplAttributes.NoInlining) == 0
        && (Aggressive(method) || method.Parameters.Count == 0 && !ManagedTypes.IsVoid(method.ReturnType)
            || method.Parameters.Count == 1 && ManagedTypes.IsVoid(method.ReturnType));
    public static bool IsInlineCandidate(ManagedBody body) => Aggressive(body.Method.Method)
        || AccessorTemplates.Read(body).Template is { SingleField: true };
    private static MethodCopySurvey Build(GlobalFacts facts)
    {
        var result = new MethodCopySurvey();
        if (facts.Architecture != "arm64") return result;
        var runtime = facts.RuntimeFunctions;
        var internalCalls = InternalCallAssembly.Get(facts).Facts;
        var watch = Stopwatch.StartNew();
        var uses = new Dictionary<ulong, HashSet<ulong>>();
        bool Eligible(ulong address) => facts.Image.IsExecutable(address) && !facts.CodeMap.ByAddress.ContainsKey(address)
            && !runtime.Entries.ContainsKey(address) && !internalCalls.Direct.ContainsKey(address) && !internalCalls.AmbiguousEntries.Contains(address);
        foreach (var entry in facts.CodeMap.Entries.Where(e => e.Method?.Method.DeclaresCilBody == true && e.Kind is EntryKind.Method or EntryKind.GenericMethod)
            .Select(e => e.Address).Distinct())
            foreach (var range in facts.FunctionsByStart[entry])
                foreach (var site in Arm64DirectCalls.InRange(facts.Image, range).Where(site => Eligible(site.Target)))
                {
                    if (!uses.TryGetValue(site.Target, out var callers)) uses.Add(site.Target, callers = []);
                    callers.Add(entry);
                }
        result.Callers = uses.ToImmutableDictionary(p => p.Key, p => p.Value.Order().ToImmutableArray());
        result.InitialTimings = result.InitialTimings.Add("调用普查", watch.Elapsed.TotalSeconds);
        var indexStarted = Stopwatch.GetTimestamp();
        var references = facts.CodeMap.Entries.Where(e => e.Method is { } method && EligibleCandidate(method.Method)
            && (e.Kind == EntryKind.Method && !GenericWitness.IsGeneric(method.Method)
                || e.Kind == EntryKind.GenericMethod && GenericWitness.IsCanonical(method)))
            .DistinctBy(e => (e.Address, e.Method)).OrderBy(e => RecoverySession.Identity(e.Method!.Method), StringComparer.Ordinal).ThenBy(e => e.Address).ToArray();
        var source = new Source(facts, result, references);
        result.Facts = new([], source.Resolve, source.Failure);
        result.InitialTimings = result.InitialTimings.Add("候选索引", (double)(Stopwatch.GetTimestamp() - indexStarted) / Stopwatch.Frequency);
        result.Ticks = watch.ElapsedTicks;
        return result;
    }
    private sealed class Activity
    {
        internal HashSet<ulong> Targets { get; } = [];
        internal HashSet<CodeEntry> Bodies { get; } = [];
        internal int RecursiveReads;
        internal Dictionary<ulong, Reason> Failures { get; } = [];
    }
    private sealed record Resolution(ImmutableArray<MethodCopyCandidate> Candidates, Reason? Failure);
    private sealed record Features(ImmutableHashSet<object> Calls, ImmutableHashSet<MetadataEntity> Metadata,
        ImmutableHashSet<AbstractSlot> Inputs, ImmutableHashSet<AbstractSlot> Returns);
    private sealed class Source
    {
        private readonly GlobalFacts facts;
        private readonly MethodCopySurvey result;
        private readonly CodeEntry[] references;
        private readonly Dictionary<ulong, ImmutableHashSet<object>> calls;
        private readonly ConcurrentDictionary<ulong, Lazy<StageResult<NativeFunction>>> native = [];
        private readonly ConcurrentDictionary<CodeEntry, StageResult<ManagedBody>> bodies = [];
        private readonly ConcurrentDictionary<ulong, Lazy<Features>> features = [];
        private readonly ConcurrentDictionary<ulong, Resolution> resolved = [];
        private readonly ThreadLocal<Activity> activity = new(() => new());
        private readonly FrontendStage frontend = new([new FrontendProvider("arm64", RecoverySession.DefaultComponents)]);
        private readonly ConcurrentDictionary<int, List<IntegerRecoveryStage>> stages = [];
        private readonly MethodBinder binder;
        private readonly MetadataSlotDecoder metadata;
        internal Source(GlobalFacts facts, MethodCopySurvey result, CodeEntry[] references)
        {
            this.facts = facts; this.result = result; this.references = references;
            binder = new(new(new FieldLayouts(facts.Spec, facts.Image.PointerWidth, facts.Image.PointerWidth), facts.Image.PointerWidth * 8), new Aapcs64());
            metadata = new(facts);
            calls = references.Select(e => e.Address).Distinct().ToDictionary(a => a, DirectCalls);
        }
        private ImmutableHashSet<object> DirectCalls(ulong address)
        {
            var targets = facts.FunctionsByStart[address].SingleOrDefault() is { } range ? Arm64FunctionIndex.Create(facts.Image, range) : null;
            return (targets ?? []).SelectMany(target => target switch
            {
                ImageFunction image when facts.CodeMap.ByAddress.TryGetValue(image.EntryOffset, out var entries) => entries.Where(e => e.Method is not null).Select(e => (object)e.Method!.Method),
                _ when facts.RuntimeFunctions.Find(target) is { } function => [(object)function.Function.MangledName],
                _ => Enumerable.Empty<object>(),
            }).ToImmutableHashSet();
        }
        private StageResult<NativeFunction> Lift(CodeEntry entry, bool registered) => native.GetOrAdd(entry.Address, _ => new(() =>
        {
            long started = Stopwatch.GetTimestamp();
            var lifted = frontend.Run(entry, new(entry.Method!.Method, entry, facts));
            Interlocked.Add(ref result.FrontendTicks, Stopwatch.GetTimestamp() - started);
            if (registered) Interlocked.Increment(ref result.Registered); else Interlocked.Increment(ref result.Targets);
            return lifted;
        })).Value;
        private Features Describe(CodeEntry entry, bool registered) => features.GetOrAdd(entry.Address, _ => new(() => DescribeCore(entry, registered))).Value;
        private Features DescribeCore(CodeEntry entry, bool registered)
        {
            var entities = ImmutableHashSet.CreateBuilder<MetadataEntity>();
            var inputs = ImmutableHashSet.CreateBuilder<AbstractSlot>();
            var returns = ImmutableHashSet.CreateBuilder<AbstractSlot>();
            if (Lift(entry, registered) is Completed<NativeFunction> lifted)
            {
                var f = lifted.Value; var context = new QueryContext(f); var locations = new LocationQuery();
                // ABI 传输项与帧保存不作为特征。读取位置与分支的依赖只用于候选排序。
                var roots = new List<Term>();
                foreach (var block in f.Blocks)
                {
                    foreach (var statement in block.Statements)
                    {
                        if (statement is MemoryRead read) roots.Add(read.Address);
                        if (statement is MemoryWrite write && context.Get(locations, new(write.Address, write.Width)) is not { IsSuccess: true, Value.Region: Region.Frame })
                            roots.AddRange([write.Address, write.Value]);
                    }
                    roots.AddRange(block.End is Return returned
                        ? returned.Results.Where(s => s.Value.Identity is not (EntryAtom or CallerValue)).Select(s => s.Value)
                        : SnapshotRewrite.Uses(block.End));
                }
                foreach (var term in SnapshotRewrite.Dependencies(roots))
                {
                    if (term.Identity is EntryAtom atom) inputs.Add(atom.Slot);
                }
                var allUses = f.Blocks.SelectMany(b => b.Statements.SelectMany(SnapshotRewrite.Uses)
                    .Concat(SnapshotRewrite.Uses(b.End)));
                foreach (var term in SnapshotRewrite.Dependencies(allUses))
                {
                    if (term.Width != f.AddressWidth) continue;
                    var location = context.Get(locations, new(term, 8));
                    if (location is { IsSuccess: true, Value.Region: Region.Image, Value.Offset: { } offset }
                        && offset >= 0 && offset <= ulong.MaxValue && metadata.Decode((ulong)offset) is { IsSuccess: true } entity) entities.Add(entity.Value);
                }
                foreach (var ret in f.Blocks.Select(b => b.End).OfType<Return>())
                    foreach (var slot in ret.Results.Where(s => s.Value.Identity is not (EntryAtom or CallerValue))) returns.Add(slot.Slot);
            }
            return new(registered ? calls[entry.Address] : DirectCalls(entry.Address), entities.ToImmutable(), inputs.ToImmutable(), returns.ToImmutable());
        }
        private int AbiDistance(CodeEntry entry, Features target)
        {
            var signature = binder.Entry(entry.Method!, entry.Kind == EntryKind.GenericMethod ? BindingEntryKind.SharedGeneric : BindingEntryKind.Ordinary).Value;
            if (signature is null) return int.MaxValue / 8;
            var inputs = signature.Slots.Parameters.SelectMany(v => v.Pieces.Select(p => p.Slot)
                .Concat(v.CopyAddress is { } copy ? [copy.Slot] : []))
                .Concat(signature.Slots.Return.BufferAddress is { } buffer ? [buffer.Slot] : []).ToHashSet();
            var outputs = signature.Slots.Return.Pieces.Select(p => p.Slot).ToHashSet();
            return target.Inputs.Except(inputs).Count() + target.Returns.Except(outputs).Count();
        }
        private static int Distance<T>(ImmutableHashSet<T> a, ImmutableHashSet<T> b) => a.Except(b).Count() + b.Except(a).Count();
        private StageResult<ManagedBody> Recover(CodeEntry entry, bool registered)
        {
            if (bodies.TryGetValue(entry, out var known)) return known;
            var mine = activity.Value!;
            if (!mine.Bodies.Add(entry)) { mine.RecursiveReads++; return Missing("method-copy.recursive", "副本恢复依赖活动中的方法体。"); }
            int before = mine.RecursiveReads;
            StageResult<ManagedBody> body;
            // 嵌套副本恢复不能重入活动中的访问器缓存；相同深度复用同一套恢复步骤。
            var stack = stages.GetOrAdd(Environment.CurrentManagedThreadId, _ => []);
            int depth = mine.Bodies.Count - 1;
            while (stack.Count <= depth) stack.Add(new(frontend));
            var recovery = stack[depth];
            long started = Stopwatch.GetTimestamp();
            try
            {
                // 索引的原生快照不交给并发恢复：每个恢复有独立的项表。
                long liftStarted = Stopwatch.GetTimestamp();
                var liftedBody = frontend.Run(entry, new(entry.Method!.Method, entry, facts));
                Interlocked.Add(ref result.FrontendTicks, Stopwatch.GetTimestamp() - liftStarted);
                body = liftedBody switch
                {
                    Completed<NativeFunction> lifted => recovery.Run(lifted.Value, new(entry.Method!.Method, entry, facts)),
                    Missing<NativeFunction> missing => new Missing<ManagedBody>(missing.Hole),
                    _ => throw new InvalidOperationException("未知的前端恢复结果"),
                };
            }
            finally { mine.Bodies.Remove(entry); Interlocked.Add(ref result.RecoveryTicks, Stopwatch.GetTimestamp() - started); }
            if (mine.RecursiveReads != before) return Missing("method-copy.recursive", "方法体恢复读取了递归截断，不能提供完整凭据。");
            return bodies.GetOrAdd(entry, body);
        }
        private static Missing<ManagedBody> Missing(string code, string message) => new(new("恢复", 0, "副本", new(code, message)));
        internal Reason? Failure(ulong address) => resolved.TryGetValue(address, out var complete) ? complete.Failure
            : activity.Value!.Failures.GetValueOrDefault(address) ?? result.Reasons.GetValueOrDefault(address);
        internal ImmutableArray<MethodCopyCandidate> Resolve(ulong address)
        {
            if (!result.Callers.ContainsKey(address)) return [];
            if (resolved.TryGetValue(address, out var known)) return known.Candidates;
            var mine = activity.Value!;
            if (!mine.Targets.Add(address))
            {
                mine.RecursiveReads++;
                mine.Failures[address] = new("method-copy.recursive", "副本身份依赖活动中的未注册目标。"); return [];
            }
            int before = mine.RecursiveReads;
            long started = Stopwatch.GetTimestamp();
            try
            {
                var found = Find(address);
                if (mine.RecursiveReads != before)
                {
                    var why = new Reason("method-copy.recursive", "候选恢复读取了递归截断，身份事实未缓存；" + found.Failure?.Message, found.Failure);
                    mine.Failures[address] = why; result.Reasons.TryAdd(address, why); return [];
                }
                known = resolved.GetOrAdd(address, found);
                mine.Failures.Remove(address);
                if (!known.Candidates.IsEmpty) { result.Facts.Complete(address, known.Candidates); result.Reasons.TryRemove(address, out _); }
                else result.Reasons[address] = known.Failure!;
                return known.Candidates;
            }
            finally
            {
                mine.Targets.Remove(address);
                if (mine.Targets.Count == 0) Interlocked.Add(ref result.Ticks, Stopwatch.GetTimestamp() - started);
            }
        }
        private Resolution Find(ulong address)
        {
            if (facts.FunctionsByStart[address].SingleOrDefault() is not { HasConsistentExtent: true })
            { return new([], new("method-copy.range", "副本目标没有一致的函数范围。")); }
            if (references.Length == 0) return new([], new("method-copy.index", "没有允许生成内联副本的注册候选。"));
            var target = new CodeEntry(address, references[0].Kind, references[0].Method, 0, null);
            if (Lift(target, false) is Missing<NativeFunction> missing)
            { return new([], new("method-copy.copy-hole", "副本一侧不能完整恢复：" + missing.Hole.Reason.Message, missing.Hole.Reason)); }
            var shape = Describe(target, false);
            // 调用集合先分桶；其他特征只排序。预算只影响发现，不提供身份凭据。
            int distance = calls.Values.Select(c => Distance(c, shape.Calls)).DefaultIfEmpty(0).Min();
            var bucket = references.Where(e => Distance(calls[e.Address], shape.Calls) == distance).ToArray();
            var ranked = bucket.Select(e => (Entry: e, Features: Describe(e, true))).Select(p => (p.Entry,
                Score: Distance(p.Features.Metadata, shape.Metadata) * 4 + AbiDistance(p.Entry, shape) + Distance(p.Features.Inputs, shape.Inputs) + Distance(p.Features.Returns, shape.Returns)))
                .OrderBy(p => p.Score).ThenBy(p => RecoverySession.Identity(p.Entry.Method!.Method), StringComparer.Ordinal).ThenBy(p => p.Entry.Address).ToArray();
            result.Counts[address] = ranked.Length;
            var candidates = ImmutableArray.CreateBuilder<MethodCopyCandidate>();
            var attempts = ImmutableArray.CreateBuilder<MethodCopyAttempt>();
            Reason? closest = null; int best = -1;
            var mine = activity.Value!;
            bool truncated = false;
            foreach (var (entry, _) in ranked.Take(MethodCopySurvey.CandidateLimit))
            {
                int checkpoint = mine.RecursiveReads;
                try
                {
                    if (!Aggressive(entry.Method!.Method))
                    {
                        var registration = Recover(entry, true);
                        if (registration is Missing<ManagedBody> unavailable)
                        {
                            var why = new Reason("method-copy.registered-hole", "访问器候选的注册体有洞：" + unavailable.Hole.Reason.Message, unavailable.Hole.Reason);
                            attempts.Add(new(entry.Address, entry.Method, why, 0));
                            if (closest is null) closest = why with { Message = $"候选 {RecoverySession.Identity(entry.Method.Method)}（注册入口 0x{entry.Address:x}）：" + why.Message };
                            continue;
                        }
                        if (!IsInlineCandidate(((Completed<ManagedBody>)registration).Value))
                        { attempts.Add(new(entry.Address, entry.Method, new("method-copy.candidate-rule", "无强制内联特性，注册体不是单字段访问器。"), 0)); continue; }
                    }
                    var copyEntry = entry with { Address = address };
                    var copy = Recover(copyEntry, false);
                    Reason? reason; int progress = 0;
                    if (copy is Missing<ManagedBody> copyHole)
                        reason = new("method-copy.copy-hole", "副本一侧有洞：" + copyHole.Hole.Reason.Message, copyHole.Hole.Reason);
                    else if (Recover(entry, true) is Missing<ManagedBody> registeredHole)
                        reason = new("method-copy.registered-hole", "注册一侧有洞：" + registeredHole.Hole.Reason.Message, registeredHole.Hole.Reason);
                    else
                    {
                        var reference = (Completed<ManagedBody>)Recover(entry, true);
                        long started = Stopwatch.GetTimestamp();
                        var comparison = ManagedBodyIsomorphism.Compare(((Completed<ManagedBody>)copy).Value, reference.Value);
                        Interlocked.Add(ref result.CompareTicks, Stopwatch.GetTimestamp() - started);
                        reason = comparison.Difference; progress = 1 + comparison.Matched;
                    }
                    attempts.Add(new(entry.Address, entry.Method!, reason, progress));
                    if (reason is null) candidates.Add(new(entry.Address, new(entry.Method, entry.Kind == EntryKind.GenericMethod
                        ? BindingEntryKind.SharedGeneric : BindingEntryKind.Ordinary, "method-copy")));
                    else if (progress > best)
                    {
                        best = progress;
                        closest = reason with { Message = $"最接近候选 {RecoverySession.Identity(entry.Method!.Method)}（注册入口 0x{entry.Address:x}）：" + reason.Message };
                    }
                }
                finally
                {
                    // 递归截断否决当前候选，不污染其他独立完成的候选。
                    if (mine.RecursiveReads != checkpoint) { truncated = true; mine.RecursiveReads = checkpoint; }
                }
            }
            if (candidates.Count == 0 && truncated) mine.RecursiveReads++;
            result.Attempts[address] = attempts.ToImmutable();
            return new(candidates.Distinct().ToImmutableArray(), candidates.Count == 0
                ? closest ?? new("method-copy.index", "索引没有可恢复的候选。") : null);
        }
    }
    internal static void Write(GlobalFacts facts, string path)
    {
        if (!values.TryGetValue(facts, out var value) || !value.IsValueCreated) return;
        var result = value.Value;
        File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(new
        {
            result.Seconds, result.Timings, result.LiftedTargets, result.LiftedRegistered, MethodCopySurvey.CandidateLimit, result.CappedTargets,
            CandidateCounts = result.CandidateCounts.OrderBy(p => p.Key).Select(p => new { Entry = p.Key, Count = p.Value }),
            Targets = result.Callers.Count, Callers = result.Callers.Values.SelectMany(x => x).Distinct().Count(),
            Copies = result.Facts.Entries.OrderBy(p => p.Key).Select(p => new { Entry = p.Key, Callers = result.Callers[p.Key],
                Candidates = p.Value.Select(c => new { c.RegisteredEntry, Method = RecoverySession.Identity(c.Entry.Method!.Method), Kind = c.Entry.Kind.ToString() }) }),
            Attempts = result.Attempts.OrderBy(p => p.Key).Select(p => new { Entry = p.Key, Candidates = p.Value.Select(a => new
            { a.RegisteredEntry, Method = RecoverySession.Identity(a.Method.Method), a.Failure, a.Matched }) }),
            Missing = result.Missing.OrderBy(p => p.Key).Select(p => new { Entry = p.Key, p.Value.Code, p.Value.Message, p.Value.Cause, Callers = result.Callers[p.Key] }),
        }, new System.Text.Json.JsonSerializerOptions { WriteIndented = true }));
    }
}
