using System.Collections.Immutable;
using System.Reflection;
using Cpp2CS.Runtime;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Inlining;

public sealed record ConstructorCall(MethodRef Method, BoundCall Binding, bool Virtual, Term? Receiver);
public sealed record AllocationConstructorRequest(Point Point, TypeRef Type, Term Result, ConstructorAccess Access);
public sealed record ConstructorInitialWrite(Point Point, MemoryWrite Write, FieldRef Field, bool AfterCall = false);
public sealed record ConstructorInitialRegion(IReadOnlyList<ConstructorInitialWrite> Writes, CallIdentity? Call = null, Point? CallPoint = null);
public sealed record AllocationConstructorAnswer(MethodRef? Constructor, CallIdentity? Call, Reason? Failure)
{
    public ConstructorInitialRegion Region { get; init; } = new([]);
    public Term? MergedResult { get; init; }
    public ImmutableArray<Term> MergedInputs { get; init; } = [];
    public ImmutableArray<Term> MergedAliases { get; init; } = [];
}

/// <summary>先配对直接构造调用，再以事件前沿证明延后分配；内联体仍由构造模板证明。</summary>
public sealed class AllocationConstructorQuery(StateQueries state, ManagedLocationQuery? locations, CallNamingQuery calls,
    IReadOnlyDictionary<CallIdentity, ConstructorCall> bindings, ConstructorQuery? constructors,
    IReadOnlyDictionary<Term, AllocationConstructorRequest>? allocations = null, ValueNamingQuery? names = null)
    : Query<AllocationConstructorRequest, AllocationConstructorAnswer>
{
    private readonly BoundSourceQuery sources = new(state);
    private readonly MergedAllocationConstructorQuery? merged = allocations is not { Count: > 0 } ? null : new(state, locations, calls, bindings, allocations, names);
    private readonly UseIndex uses = new(state, calls);
    public override Outcome<AllocationConstructorAnswer> Compute(QueryContext c, AllocationConstructorRequest key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<AllocationConstructorAnswer>();
        var block = index.Value.Blocks[key.Point.Block]; int next = key.Point.Before + 1;
        while (next < block.Statements.Length && block.Statements[next] is not Call && PrivateAccess(c, state, locations, block.Statements[next])) next++;
        if (next < block.Statements.Length && block.Statements[next] is Call call && Direct(c, new(block.Identity, next), call, key) is { } method)
            return Outcome<AllocationConstructorAnswer>.Success(new(method, call.Identity, null));
        var deferred = DeferredCall(c, key);
        if (deferred is not null)
        {
            if (deferred.Failure is { } rejected) constructors?.Reject(key.Access, rejected);
            return Outcome<AllocationConstructorAnswer>.Success(deferred);
        }
        if (constructors is null) return Outcome<AllocationConstructorAnswer>.Success(TryMerged(c, key) ?? new(null, null,
            new("lowering.Allocation.Constructor", "对象分配之后的第一个事件不是对它的同类构造函数调用。")));
        var initial = InitialRegion(c, new(block.Identity, key.Point.Before + 1), key.Result);
        if (initial.Call is { } delayed && bindings[delayed].Method.DeclaringType.Equals(key.Type)) return Deferred(null);
        var included = initial.Writes.Select(w => w.Write.Identity).ToHashSet();
        var frontier = new EventFrontierQuery((context, point) => Uses(context, point, key, included));
        var reached = c.Get(frontier, new(new(block.Identity, key.Point.Before + 1)));
        if (!reached.IsSuccess) return Unproved(reached.Why);
        if (reached.Value.HasCycle || reached.Value.ReachesExit || reached.Value.Stops.Count == 0) return Unproved(null);
        foreach (var point in reached.Value.Stops)
        {
            var at = index.Value.Blocks[point.Block];
            if (point.Before < at.Statements.Length && at.Statements[point.Before] is Call candidate
                && bindings.TryGetValue(candidate.Identity, out var target)
                && target.Method.Method is { Name: ".ctor", IsStatic: false } && target.Method.DeclaringType.Equals(key.Type)) return Deferred(null);
        }
        return Outcome<AllocationConstructorAnswer>.Success(new(null, null, null)
        { Region = initial });
        Outcome<AllocationConstructorAnswer> Reject(string code, string message, Reason? cause)
        {
            if (TryMerged(c, key) is { } answer)
            {
                if (answer.Failure is { } failure) constructors.Reject(key.Access, failure);
                return Outcome<AllocationConstructorAnswer>.Success(answer);
            }
            var reason = new Reason(code, message, cause);
            constructors.Reject(key.Access, reason);
            return Outcome<AllocationConstructorAnswer>.Success(new(null, null, reason));
        }
        Outcome<AllocationConstructorAnswer> Deferred(Reason? cause) => Reject("lowering.Allocation.Deferred", "对象首次使用是构造调用，但分配移动尚未证明。", cause);
        Outcome<AllocationConstructorAnswer> Unproved(Reason? cause) => Reject("lowering.Allocation.Constructor", "不能证明各路径的首次对象使用都不是构造调用。", cause);
    }
    private sealed record UsesAt(SemanticUses Semantics, IReadOnlyDictionary<Point, SemanticUses.Use[]> Roots);
    private sealed class UseIndex(StateQueries state, CallNamingQuery calls) : Query<int, UsesAt>
    {
        public override Outcome<UsesAt> Compute(QueryContext c, int key)
        {
            var uses = new SemanticUses(c, calls, state);
            return Outcome<UsesAt>.Success(new(uses, uses.Roots.GroupBy(u => u.Point).ToDictionary(g => g.Key, g => g.ToArray())));
        }
    }

    /// <summary>只接受同一次正常构造续点；登记过的检查抛出是异常停点，不是普通退出。</summary>
    private AllocationConstructorAnswer? DeferredCall(QueryContext c, AllocationConstructorRequest key)
    {
        if (!bindings.Values.Any(b => b.Method.Method is { Name: ".ctor", IsStatic: false } && b.Method.DeclaringType.Equals(key.Type))) return null;
        var indexed = c.Get(state.Index, 0); if (!indexed.IsSuccess) return null;
        var semantic = c.Get(uses, 0); if (!semantic.IsSuccess) return null;
        var resolved = c.Get(state.Resolve, key.Result); if (!resolved.IsSuccess) return null;
        var allocation = indexed.Value.Blocks[key.Point.Block].Statements[key.Point.Before] as Call;
        if (allocation is null || allocation.DoesNotReturn) return null;
        bool relaxed = key.Type is DefinitionRef type && ((type.Definition.Attributes & TypeAttributes.BeforeFieldInit) != 0
            || !type.Definition.Methods.Any(m => m.Name == ".cctor"));
        Reason? barrier = null;
        var exceptional = new HashSet<Point>();
        var candidates = new Dictionary<Point, (Call Call, MethodRef Method)>();
        Outcome<bool> Stop(QueryContext context, Point point)
        {
            var block = indexed.Value.Blocks[point.Block];
            var statement = point.Before < block.Statements.Length ? block.Statements[point.Before] : null;
            if (statement is Call call && Direct(context, point, call, key) is { } constructor)
            {
                candidates.Add(point, (call, constructor));
                if (call.Unwind != allocation.Unwind)
                    barrier ??= new("lowering.Allocation.Deferred.ExceptionRegion", "分配与构造调用的异常处理目标不同。");
                return Outcome<bool>.Success(true);
            }
            // 私有溢出不是对象暴露；后续的实际输入由读取身份解析。
            bool privateAccess = statement is MemoryRead or MemoryWrite
                && UnescapedFrameAccess(context, state, statement) is { IsSuccess: true, Value: true };
            if (!privateAccess && semantic.Value.Roots.TryGetValue(point, out var roots))
                foreach (var root in roots)
                {
                    var value = context.Get(state.Resolve, root.Value); if (!value.IsSuccess) return value.Propagate<bool>();
                    bool used = false, unresolved = false;
                    semantic.Value.Semantics.Visit(value.Value, (term, _, _) =>
                    { used |= term == resolved.Value; unresolved |= term.Identity is MemoryMerge; });
                    if (used) return Outcome<bool>.Success(true);
                    if (unresolved) return Outcome<bool>.Failure(new("inline.Constructor.Use", "对象使用含未解析的内存合流来源。"));
                }
            if (statement is null || privateAccess) return Outcome<bool>.Success(false);
            if (block.Handler is not null)
                barrier ??= new("lowering.Allocation.Deferred.ExceptionRegion", "分配移动经过异常处理入口。");
            if (statement is Call other)
            {
                var named = context.Get(calls, other.Identity); if (!named.IsSuccess) return named.Propagate<bool>();
                if (other.Unwind is not null)
                    barrier ??= new("lowering.Allocation.Deferred.ExceptionRegion", "中间调用含尚未证明的异常边。");
                if (named.Value.Operation?.FixedThrownException is not null)
                {
                    if (!relaxed) InitializationBarrier();
                    exceptional.Add(point); return Outcome<bool>.Success(true);
                }
                if (other.DoesNotReturn)
                    barrier ??= new("lowering.Allocation.Deferred.ExceptionRegion", "中间调用不返回。");
                if (named.Value.Operation is { Observation: RuntimeObservation.Unobservable }) return Outcome<bool>.Success(false);
                if (!relaxed) InitializationBarrier();
                if (!bindings.ContainsKey(other.Identity) && named.Value.Binding is null)
                    barrier ??= new("lowering.Allocation.Deferred.Binding", "中间调用没有完整的有效输入绑定。");
                return Outcome<bool>.Success(false);
            }
            if (statement is MemoryRead read && !read.Acquire && locations is not null)
            {
                var location = context.Get(locations, new(read.Address, read.Width));
                if (!location.IsSuccess) return location.Propagate<bool>();
                if (location.Value.Kind is not (ManagedLocationKind.Unknown or ManagedLocationKind.NotManaged))
                {
                    if (!relaxed) InitializationBarrier();
                    return Outcome<bool>.Success(false);
                }
                if (names is not null)
                {
                    var fixedValue = names.FixedValue(context, read.Result);
                    if (fixedValue.IsSuccess && fixedValue.Value is EntityName) return Outcome<bool>.Success(false);
                    if (fixedValue.IsSuccess && fixedValue.Value is FieldName or ArrayElementName)
                    {
                        if (!relaxed) InitializationBarrier();
                        return Outcome<bool>.Success(false);
                    }
                }
                // 规格命名的运行时状态读取有安全地址凭据，仍不能越过精确类初始化。
                if (names is not null && context.Get(names, read.Result) is { IsSuccess: true, Value.Name: FieldName or ArrayElementName })
                {
                    if (!relaxed) InitializationBarrier();
                    return Outcome<bool>.Success(false);
                }
            }
            barrier ??= new("lowering.Allocation.Deferred.Access", "分配与构造之间有未证明可移动的访问或操作。");
            return Outcome<bool>.Success(false);
        }
        void InitializationBarrier() => barrier ??= new("lowering.Allocation.Deferred.ClassInitialization",
            "所分配类的静态初始化可观察，不能越过中间的事件或托管读取。");
        var frontier = new EventFrontierQuery(Stop);
        var reached = c.Get(frontier, new(new(key.Point.Block, key.Point.Before + 1)));
        if (!reached.IsSuccess || candidates.Count == 0) return null;
        AllocationConstructorAnswer No(string code, string message) => new(null, null, new(code, message, barrier));
        var normal = reached.Value.Stops.Except(exceptional).ToArray();
        if (reached.Value.HasCycle || reached.Value.ReachesExit || normal.Length != 1)
            return No("lowering.Allocation.Deferred.Flow", "分配之后存在循环、普通退出或不同的构造续点。");
        if (!candidates.TryGetValue(normal[0], out var paired))
            return No("lowering.Allocation.Deferred.Use", "对象在构造调用之前已被使用。");
        if (barrier is not null) return new(null, null, barrier);
        return new(paired.Method, paired.Call.Identity, null);
    }

    internal static Outcome<bool> UnescapedFrameAccess(QueryContext c, StateQueries state, Statement statement)
    {
        var (address, width) = statement switch
        { MemoryRead read => (read.Address, read.Width), MemoryWrite write => (write.Address, write.Width), _ => (null, 0) };
        if (address is null) return Outcome<bool>.Success(false);
        var resolved = c.Get(state.Resolve, address); if (!resolved.IsSuccess) return resolved.Propagate<bool>();
        var location = c.Get(state.Locations, new(resolved.Value, width)); if (!location.IsSuccess) return location.Propagate<bool>();
        if (location.Value.Region != Region.Frame) return Outcome<bool>.Success(false);
        var escaped = c.Get(state.Escapes, 0);
        return escaped.IsSuccess ? Outcome<bool>.Success(!escaped.Value.MayReach(location.Value)) : escaped.Propagate<bool>();
    }

    private AllocationConstructorAnswer? TryMerged(QueryContext c, AllocationConstructorRequest key)
    {
        if (merged is null) return null;
        AllocationConstructorAnswer? rejected = null;
        foreach (var b in c.Snapshot.Blocks)
            foreach (var merge in b.Merges)
            {
                if (merge.Result.Width != key.Result.Width) continue;
                bool directInput = merge.Inputs.Any(i => c.Get(state.Resolve, i.Value) is { IsSuccess: true } input && input.Value == key.Result);
                if (!directInput)
                {
                    var sources = c.Get(merged.Sources, merge.Result);
                    if (!sources.IsSuccess || !sources.Value.Inputs.Any(i => i.Result == key.Result)) continue;
                }
                var result = c.Get(merged, new(b.Identity, merge));
                var answer = result.IsSuccess ? result.Value : new AllocationConstructorAnswer(null, null,
                    new("lowering.Allocation.Merge.Proof", "新分配合流的配对证明失败。", result.Why));
                if (answer.Failure is null) return answer;
                rejected ??= answer;
            }
        return rejected;
    }
    /// <summary>只沿唯一前驱的直线后继收集；一次同对象直接构造调用划分写入的前后两段。</summary>
    public ConstructorInitialRegion InitialRegion(QueryContext c, Point start, Term receiver)
    {
        var indexed = c.Get(state.Index, 0);
        if (!indexed.IsSuccess || locations is null) return new([]);
        var resolved = c.Get(state.Resolve, receiver);
        if (!resolved.IsSuccess) return new([]);
        var block = indexed.Value.Blocks[start.Block];
        var writes = new List<ConstructorInitialWrite>();
        CallIdentity? paired = null; Point? callPoint = null;
        var visited = new HashSet<BlockIdentity> { start.Block };
        for (int i = start.Before; ; i++)
        {
            if (i == block.Statements.Length)
            {
                if (block.End is not Jump jump || indexed.Value.Predecessors[jump.Target].Length != 1 || !visited.Add(jump.Target)) break;
                block = indexed.Value.Blocks[jump.Target]; i = -1; continue;
            }
            var statement = block.Statements[i];
            if (statement is Call call && paired is null && !call.DoesNotReturn && call.Unwind is null
                && bindings.TryGetValue(call.Identity, out var target) && !target.Virtual && target.Receiver is null
                && target.Method.Method is { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
                && target.Binding.This is { } self)
            {
                var source = c.Get(sources, new(self.Source, new(block.Identity, i)));
                if (!source.IsSuccess) break;
                var actual = c.Get(state.Resolve, source.Value);
                if (!actual.IsSuccess || actual.Value != resolved.Value) break;
                bool independent = true;
                foreach (var parameter in target.Binding.Parameters)
                {
                    var input = c.Get(sources, new(parameter.Source, new(block.Identity, i)));
                    if (!input.IsSuccess) { independent = false; break; }
                    var value = c.Get(state.Resolve, input.Value);
                    if (!value.IsSuccess || SnapshotRewrite.Dependencies([value.Value]).Contains(resolved.Value)) { independent = false; break; }
                }
                if (!independent) break;
                paired = call.Identity; callPoint = new(block.Identity, i); continue;
            }
            if (statement is MemoryWrite write)
            {
                var value = c.Get(state.Resolve, write.Value);
                if (!value.IsSuccess || SnapshotRewrite.Dependencies([value.Value]).Contains(resolved.Value)) break;
                var location = c.Get(locations, new(write.Address, write.Width));
                if (location.IsSuccess)
                {
                    var views = location.Value.Views.Where(v => v.Kind == ManagedLocationKind.InstanceField && v.Path.Length == 1
                        && v.Offset == 0 && v.Width == write.Width
                        && locations.Layouts.TrySizeAndAlignment(v.Type) is { } size && size.Size * 8 == write.Width).ToArray();
                    if (views is [var view])
                    {
                        var root = c.Get(state.Resolve, view.Root);
                        if (root.IsSuccess && root.Value == resolved.Value)
                        {
                            var current = c.Get(state.Resolve, write.Address);
                            if (!current.IsSuccess) break;
                            var at = c.Get(state.Locations, new(current.Value, write.Width));
                            if (!at.IsSuccess) break;
                            bool disjoint = true;
                            foreach (var previous in writes.Where(w => !w.Field.Equals(view.Path[0])))
                            {
                                var address = c.Get(state.Resolve, previous.Write.Address);
                                if (!address.IsSuccess) { disjoint = false; break; }
                                var before = c.Get(state.Locations, new(address.Value, previous.Write.Width));
                                if (!before.IsSuccess) { disjoint = false; break; }
                                var overlap = c.Get(state.Alias, new(at.Value, before.Value));
                                if (!overlap.IsSuccess || overlap.Value.Kind != AliasKind.Disjoint) { disjoint = false; break; }
                            }
                            if (!disjoint) break;
                            writes.Add(new(new(block.Identity, i), write, view.Path[0], paired is not null)); continue;
                        }
                    }
                }
                if (!PrivateAccess(c, state, locations, write)) break;
            }
            else if (!PrivateAccess(c, state, locations, statement)) break;
        }
        return new(writes, paired, callPoint);
    }
    internal MethodRef? Direct(QueryContext c, Point point, Call call, AllocationConstructorRequest key)
    {
        if (!bindings.TryGetValue(call.Identity, out var target) || target.Virtual || target.Receiver is not null
            || target.Method.Method is not { Name: ".ctor", IsStatic: false } || !target.Method.DeclaringType.Equals(key.Type)
            || target.Binding.This is not { } self) return null;
        var receiver = c.Get(sources, new(self.Source, point));
        if (!receiver.IsSuccess) return null;
        var actual = c.Get(state.Resolve, receiver.Value); var expected = c.Get(state.Resolve, key.Result);
        return actual.IsSuccess && expected.IsSuccess && actual.Value == expected.Value ? target.Method : null;
    }
    private Outcome<bool> Uses(QueryContext c, Point point, AllocationConstructorRequest key, HashSet<WriteIdentity> included)
    {
        var indexed = c.Get(state.Index, 0); if (!indexed.IsSuccess) return indexed.Propagate<bool>();
        var block = indexed.Value.Blocks[point.Block];
        IEnumerable<Term> uses;
        if (point.Before == block.Statements.Length) uses = SnapshotRewrite.Uses(block.End);
        else
        {
            var statement = block.Statements[point.Before];
            if (statement is MemoryWrite written && included.Contains(written.Identity)) return Outcome<bool>.Success(false);
            if (statement is MemoryWrite or MemoryRead && PrivateAccess(c, state, locations, statement)) return Outcome<bool>.Success(false);
            if (statement is Call call)
            {
                var arguments = new List<Term>();
                IEnumerable<BoundValue> inputs;
                if (bindings.TryGetValue(call.Identity, out var binding))
                {
                    inputs = binding.Binding.Parameters;
                    if (binding.Receiver is { } receiver) arguments.Add(receiver);
                    else if (binding.Binding.This is { } self) inputs = inputs.Prepend(self);
                }
                else
                {
                    var classified = c.Get(calls, call.Identity); if (!classified.IsSuccess) return classified.Propagate<bool>();
                    if (classified.Value.Binding is not { } bound)
                        return Outcome<bool>.Failure(new("inline.Constructor.Use", "调用的有效输入尚未绑定。"));
                    inputs = bound.Arguments;
                }
                foreach (var input in inputs)
                {
                    var source = c.Get(sources, new(input.Source, point)); if (!source.IsSuccess) return source.Propagate<bool>();
                    arguments.Add(source.Value);
                }
                uses = arguments;
            }
            else uses = SnapshotRewrite.Uses(statement);
        }
        foreach (var use in uses)
        {
            var resolved = c.Get(state.Resolve, use); if (!resolved.IsSuccess) return resolved.Propagate<bool>();
            var dependencies = SnapshotRewrite.Dependencies([resolved.Value]);
            if (dependencies.Contains(key.Result)) return Outcome<bool>.Success(true);
            if (dependencies.Any(t => t.Identity is MemoryMerge or ResultAtom { Definition: MergeIdentity }))
                return Outcome<bool>.Failure(new("inline.Constructor.Use", "首次使用含未解析的合流来源。"));
        }
        return Outcome<bool>.Success(false);
    }
    public static bool PrivateAccess(QueryContext c, StateQueries state, ManagedLocationQuery? locations, Statement statement)
    {
        var (address, width, read) = statement switch
        {
            MemoryRead r => (r.Address, r.Width, true), MemoryWrite w => (w.Address, w.Width, false), _ => (null, 0, false),
        };
        if (address is null) return false;
        var resolved = c.Get(state.Resolve, address); if (!resolved.IsSuccess) return false;
        var location = c.Get(state.Locations, new(resolved.Value, width)); if (!location.IsSuccess) return false;
        if (location.Value.Region == Region.Frame) return true;
        if (!read || locations is null) return false;
        var managed = c.Get(locations, new(address, width));
        return managed.IsSuccess && managed.Value.Kind == ManagedLocationKind.NotManaged;
    }
}
