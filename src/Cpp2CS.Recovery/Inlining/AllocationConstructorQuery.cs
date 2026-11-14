using System.Collections.Immutable;
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

/// <summary>直线配对与模板锚点沿用原条件；未配对的同类新分配可由合流前沿证明。</summary>
public sealed class AllocationConstructorQuery(StateQueries state, ManagedLocationQuery? locations, CallNamingQuery calls,
    IReadOnlyDictionary<CallIdentity, ConstructorCall> bindings, ConstructorQuery? constructors,
    IReadOnlyDictionary<Term, AllocationConstructorRequest>? allocations = null, ValueNamingQuery? names = null)
    : Query<AllocationConstructorRequest, AllocationConstructorAnswer>
{
    private readonly BoundSourceQuery sources = new(state);
    private readonly MergedAllocationConstructorQuery? merged = allocations is not { Count: > 0 } ? null : new(state, locations, calls, bindings, allocations, names);
    public override Outcome<AllocationConstructorAnswer> Compute(QueryContext c, AllocationConstructorRequest key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<AllocationConstructorAnswer>();
        var block = index.Value.Blocks[key.Point.Block]; int next = key.Point.Before + 1;
        while (next < block.Statements.Length && block.Statements[next] is not Call && PrivateAccess(c, state, locations, block.Statements[next])) next++;
        if (next < block.Statements.Length && block.Statements[next] is Call call && Direct(c, new(block.Identity, next), call, key) is { } method)
            return Outcome<AllocationConstructorAnswer>.Success(new(method, call.Identity, null));
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
        Outcome<AllocationConstructorAnswer> Deferred(Reason? cause) => Reject("lowering.Allocation.Deferred", "对象首次使用是构造调用，但不满足紧邻配对条件。", cause);
        Outcome<AllocationConstructorAnswer> Unproved(Reason? cause) => Reject("lowering.Allocation.Constructor", "不能证明各路径的首次对象使用都不是构造调用。", cause);
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
