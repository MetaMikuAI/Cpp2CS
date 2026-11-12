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
public sealed record ConstructorInitialWrite(Point Point, MemoryWrite Write, FieldRef Field);
public sealed record AllocationConstructorAnswer(MethodRef? Constructor, CallIdentity? Call, Reason? Failure)
{
    public IReadOnlyList<ConstructorInitialWrite> Writes { get; init; } = [];
}

/// <summary>紧邻配对沿用原条件；模板锚点保留共享前沿对延迟构造调用的保护。</summary>
public sealed class AllocationConstructorQuery(StateQueries state, ManagedLocationQuery? locations, CallNamingQuery calls,
    IReadOnlyDictionary<CallIdentity, ConstructorCall> bindings, ConstructorQuery? constructors)
    : Query<AllocationConstructorRequest, AllocationConstructorAnswer>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<AllocationConstructorAnswer> Compute(QueryContext c, AllocationConstructorRequest key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<AllocationConstructorAnswer>();
        var block = index.Value.Blocks[key.Point.Block]; int next = key.Point.Before + 1;
        while (next < block.Statements.Length && block.Statements[next] is not Call && PrivateAccess(c, state, locations, block.Statements[next])) next++;
        if (next < block.Statements.Length && block.Statements[next] is Call call && Direct(c, new(block.Identity, next), call, key) is { } method)
            return Outcome<AllocationConstructorAnswer>.Success(new(method, call.Identity, null));
        if (constructors is null) return Outcome<AllocationConstructorAnswer>.Success(new(null, null,
            new("lowering.Allocation.Constructor", "对象分配之后的第一个事件不是对它的同类构造函数调用。")));
        var initial = InitialWrites(c, new(block.Identity, key.Point.Before + 1), key.Result);
        var included = initial.Select(w => w.Write.Identity).ToHashSet();
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
        { Writes = initial });
        Outcome<AllocationConstructorAnswer> Reject(string code, string message, Reason? cause)
        {
            var reason = new Reason(code, message, cause);
            constructors.Reject(key.Access, reason);
            return Outcome<AllocationConstructorAnswer>.Success(new(null, null, reason));
        }
        Outcome<AllocationConstructorAnswer> Deferred(Reason? cause) => Reject("lowering.Allocation.Deferred", "对象首次使用是构造调用，但不满足紧邻配对条件。", cause);
        Outcome<AllocationConstructorAnswer> Unproved(Reason? cause) => Reject("lowering.Allocation.Constructor", "不能证明各路径的首次对象使用都不是构造调用。", cause);
    }
    /// <summary>只读取当前基本块的初始写入；分支、汇合、调用与托管读取均截断，不重排控制流。</summary>
    public IReadOnlyList<ConstructorInitialWrite> InitialWrites(QueryContext c, Point start, Term receiver)
    {
        var indexed = c.Get(state.Index, 0);
        if (!indexed.IsSuccess || locations is null) return [];
        var resolved = c.Get(state.Resolve, receiver);
        if (!resolved.IsSuccess) return [];
        var block = indexed.Value.Blocks[start.Block];
        var writes = new List<ConstructorInitialWrite>();
        for (int i = start.Before; i < block.Statements.Length; i++)
        {
            var statement = block.Statements[i];
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
                            writes.Add(new(new(start.Block, i), write, view.Path[0])); continue;
                        }
                    }
                }
                if (!PrivateAccess(c, state, locations, write)) break;
            }
            else if (!PrivateAccess(c, state, locations, statement)) break;
        }
        return writes;
    }
    private MethodRef? Direct(QueryContext c, Point point, Call call, AllocationConstructorRequest key)
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
