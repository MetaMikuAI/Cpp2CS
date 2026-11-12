using System.Collections.Immutable;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Checks;

public sealed record ThrowOnly(string Exception, ImmutableHashSet<Point> Throws);
public sealed record CheckSubject(Term? Value = null, Term? Index = null, Term? Length = null, Term? Array = null);
public sealed record ConditionalCheck(FlowEdge FailureEdge, FlowEdge PassEdge, string Exception, Term FailureCondition,
    CheckSubject Subject, bool CanAbsorb, ImmutableHashSet<Point> Accesses, Reason? ExplicitReason);
public sealed record CheckPoint(bool Event, bool HeapWrite, ImmutableArray<LocationView> Locations, ImmutableArray<Term> Divisors, Term? Receiver);

/// <summary>函数级查询；使用位置查询的上下文。只读取快照，不删除分支、调用或访问。</summary>
public sealed class CheckQueries
{
    internal readonly StateQueries State;
    internal readonly CallNamingQuery Calls;
    internal readonly ManagedLocationQuery Locations;
    internal readonly Query<CallIdentity, Term?>? DispatchReceiver;
    internal ManagedCallAddressQuery Addresses { get; }
    public CheckPointQuery Points { get; }
    public ThrowOnlyQuery ThrowOnly { get; }
    public ConditionalCheckQuery Checks { get; }
    internal EventFrontierQuery Events { get; }
    internal EventFrontierQuery AccessFrontier { get; }
    /// <param name="dispatchReceiver">分派查询证明为虚调用或接口调用的接收者；没有证明时返回 null。</param>
    public CheckQueries(StateQueries state, CallNamingQuery calls, ManagedLocationQuery locations, Query<CallIdentity, Term?>? dispatchReceiver = null)
    {
        State = state; Calls = calls; Locations = locations; DispatchReceiver = dispatchReceiver;
        Addresses = new(state, calls, locations);
        Points = new(this);
        Events = new((c, p) => Stop(c, p, false));
        AccessFrontier = new((c, p) => Stop(c, p, true));
        ThrowOnly = new(this); Checks = new(this);
    }
    private Outcome<bool> Stop(QueryContext c, Point p, bool access)
    {
        if (!access)
        {
            var statement = Statement(c, p);
            if (statement is Call call)
            {
                var named = c.Get(Calls, call.Identity);
                return named.IsSuccess ? Outcome<bool>.Success(named.Value.Operation is not { Observation: RuntimeObservation.Unobservable }) : named.Propagate<bool>();
            }
            if (statement is TrapWhen or DynamicAllocation) return Outcome<bool>.Success(true);
            if (statement is not MemoryWrite) return Outcome<bool>.Success(false);
        }
        var r = c.Get(Points, p);
        return r.IsSuccess ? Outcome<bool>.Success(r.Value.Event || r.Value.HeapWrite ||
            access && (r.Value.Locations.Length > 0 || r.Value.Divisors.Length > 0)) : r.Propagate<bool>();
    }
    internal static Statement? Statement(QueryContext c, Point p)
    {
        var b = c.Snapshot.Blocks.Single(b => b.Identity == p.Block);
        return p.Before < b.Statements.Length ? b.Statements[p.Before] : null;
    }
}

public sealed class CheckPointQuery(CheckQueries q) : Query<Point, CheckPoint>
{
    public override Outcome<CheckPoint> Compute(QueryContext c, Point key)
    {
        var b = c.Snapshot.Blocks.Single(b => b.Identity == key.Block);
        var s = CheckQueries.Statement(c, key);
        bool observable = s is TrapWhen or DynamicAllocation, write = false;
        ImmutableArray<LocationView> views = []; Term? receiver = null;
        if (s is Call call)
        {
            var named = c.Get(q.Calls, call.Identity); if (!named.IsSuccess) return named.Propagate<CheckPoint>();
            observable = named.Value.Operation is not { Observation: RuntimeObservation.Unobservable };
            var addresses = c.Get(q.Addresses, call.Identity); if (!addresses.IsSuccess) return addresses.Propagate<CheckPoint>();
            views = addresses.Value;
            if (q.DispatchReceiver is { } dispatch)
            {
                var r = c.Get(dispatch, call.Identity); if (!r.IsSuccess) return r.Propagate<CheckPoint>();
                if (r.Value is { } value)
                {
                    var resolved = c.Get(q.State.Resolve, value); if (!resolved.IsSuccess) return resolved.Propagate<CheckPoint>();
                    receiver = resolved.Value;
                }
            }
        }
        var request = s switch { MemoryRead r => new AddressRequest(r.Address, r.Width), MemoryWrite w => new AddressRequest(w.Address, w.Width), _ => default };
        if (request.Address is not null)
        {
            var resolved = c.Get(q.State.Resolve, request.Address); if (!resolved.IsSuccess) return resolved.Propagate<CheckPoint>();
            var native = c.Get(q.State.Locations, new(resolved.Value, request.Width)); if (!native.IsSuccess) return native.Propagate<CheckPoint>();
            if (native.Value.Region != Region.Frame)
            {
                var located = c.Get(q.Locations, request); if (!located.IsSuccess) return located.Propagate<CheckPoint>();
                views = located.Value.Views;
                // 写入会在延后的异常处被观察；没有不可观察区域依据时不能跨过。
                write = s is MemoryWrite && located.Value.Kind != ManagedLocationKind.NotManaged;
            }
        }
        IEnumerable<Term> uses = s switch
        {
            MemoryRead r => [r.Address], MemoryWrite w => [w.Address, w.Value], TrapWhen t => [t.Condition],
            Call x => x.Arguments.Select(a => a.Value), DynamicAllocation d => [d.Size],
            _ => b.End switch { Return r => r.Results.Select(x => x.Value), Branch x => [x.Condition], JumpTable x => [x.Selector], ResumeUnwind x => [x.Exception], _ => [] }
        };
        var divisors = ImmutableArray.CreateBuilder<Term>(); var pending = new Stack<Term>(); var seen = new HashSet<Term>();
        foreach (var use in uses)
        {
            var resolved = c.Get(q.State.Resolve, use); if (!resolved.IsSuccess) return resolved.Propagate<CheckPoint>();
            pending.Push(resolved.Value);
        }
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            if (c.Step() is { } why) return Outcome<CheckPoint>.Failure(why);
            if (term.Operator is CoreOperator { Operation: CoreOperation.SignedDivide or CoreOperation.UnsignedDivide or CoreOperation.SignedRemainder or CoreOperation.UnsignedRemainder })
            {
                var d = c.Get(q.State.Resolve, term.Operands[1]); if (!d.IsSuccess) return d.Propagate<CheckPoint>();
                divisors.Add(d.Value);
            }
            // select 的未选分支不一定求值。
            foreach (var child in term.Operator is CoreOperator { Operation: CoreOperation.Select } ? term.Operands.Take(1) : term.Operands)
                pending.Push(child);
        }
        return Outcome<CheckPoint>.Success(new(observable, write, views, divisors.ToImmutable(), receiver));
    }
}

public sealed class ThrowOnlyQuery(CheckQueries q) : Query<BlockIdentity, ThrowOnly?>
{
    public override Outcome<ThrowOnly?> Compute(QueryContext c, BlockIdentity key)
    {
        var frontier = c.Get(q.Events, new(new(key, 0))); if (!frontier.IsSuccess) return frontier.Propagate<ThrowOnly?>();
        var f = frontier.Value;
        if (f.ReachesExit || f.HasCycle || f.Stops.Count == 0) return Outcome<ThrowOnly?>.Success(null);
        string? exception = null;
        foreach (var point in f.Stops)
        {
            if (CheckQueries.Statement(c, point) is not Call { Unwind: null } call) return Outcome<ThrowOnly?>.Success(null);
            var named = c.Get(q.Calls, call.Identity); if (!named.IsSuccess) return named.Propagate<ThrowOnly?>();
            if (named.Value.Operation is not { DoesNotReturn: true, Termination: RuntimeTermination.Throw, FixedThrownException: { } type })
                return Outcome<ThrowOnly?>.Success(null);
            if (exception is not null && exception != type) return Outcome<ThrowOnly?>.Success(null);
            exception = type;
        }
        return Outcome<ThrowOnly?>.Success(new(exception!, f.Stops));
    }
}

public sealed class ConditionalCheckQuery(CheckQueries q) : Query<FlowEdge, ConditionalCheck?>
{
    public override Outcome<ConditionalCheck?> Compute(QueryContext c, FlowEdge key)
    {
        var block = c.Snapshot.Blocks.Single(b => b.Identity == key.Source);
        if (block.End is not Branch branch || branch.True == branch.False || key.Target != branch.True && key.Target != branch.False)
            return Outcome<ConditionalCheck?>.Success(null);
        var throwing = c.Get(q.ThrowOnly, key.Target); if (!throwing.IsSuccess) return throwing.Propagate<ConditionalCheck?>();
        if (throwing.Value is not { } only) return Outcome<ConditionalCheck?>.Success(null);
        var resolved = c.Get(q.State.Resolve, branch.Condition); if (!resolved.IsSuccess) return resolved.Propagate<ConditionalCheck?>();
        bool trueEdge = key.Target == branch.True;
        var condition = trueEdge ? resolved.Value : c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, resolved.Value);
        var subject = Subject(c, resolved.Value, trueEdge, only.Exception); if (!subject.IsSuccess) return subject.Propagate<ConditionalCheck?>();
        var pass = new FlowEdge(key.Source, trueEdge ? branch.False : branch.True);
        Outcome<ConditionalCheck?> Result(bool absorb, ImmutableHashSet<Point> accesses, string? code = null, string? text = null) =>
            Outcome<ConditionalCheck?>.Success(new(key, pass, only.Exception, condition, subject.Value, absorb, accesses,
                code is null ? null : new("check." + code, text!)));
        if (subject.Value.Value is null && subject.Value.Array is null)
            return Result(false, [], "subject", "条件没有可用于吸收的对象。");
        var frontier = c.Get(q.AccessFrontier, FrontierStart.FromEdge(pass)); if (!frontier.IsSuccess) return frontier.Propagate<ConditionalCheck?>();
        if (frontier.Value.HasCycle) return Result(false, [], "cycle", "在访问前可能进入循环。");
        if (frontier.Value.ReachesExit || frontier.Value.Stops.Count == 0) return Result(false, [], "no-access", "有路径在匹配访问前到达结局。");
        foreach (var p in frontier.Value.Stops)
        {
            var info = c.Get(q.Points, p); if (!info.IsSuccess) return info.Propagate<ConditionalCheck?>();
            bool matched = only.Exception == "System.DivideByZeroException" && info.Value.Divisors.Contains(subject.Value.Value!) ||
                only.Exception == "System.NullReferenceException" && info.Value.Receiver is { } receiver && receiver == subject.Value.Value;
            foreach (var v in info.Value.Locations)
            {
                var root = c.Get(q.State.Resolve, v.Root); if (!root.IsSuccess) return root.Propagate<ConditionalCheck?>();
                if (only.Exception == "System.NullReferenceException" && v.Kind is ManagedLocationKind.InstanceField or ManagedLocationKind.ArrayLength or ManagedLocationKind.ArrayElement)
                    matched |= root.Value == subject.Value.Value;
                if (only.Exception == "System.IndexOutOfRangeException" && v.Kind == ManagedLocationKind.ArrayElement && root.Value == subject.Value.Array && v.Index is { } index)
                {
                    var i = c.Get(q.State.Resolve, index); if (!i.IsSuccess) return i.Propagate<ConditionalCheck?>();
                    matched |= i.Value == subject.Value.Index;
                }
            }
            if (!matched) return Result(false, [], info.Value.Event ? "event" : info.Value.HeapWrite ? "write" : "different-access",
                info.Value.Event ? "匹配访问前有可观察事件。" : info.Value.HeapWrite ? "匹配访问前的写入会被异常观察。" : "前沿访问的对象或下标不相同。");
        }
        return Result(true, frontier.Value.Stops);
    }
    private Outcome<CheckSubject> Subject(QueryContext c, Term condition, bool positive, string exception)
    {
        Outcome<CheckSubject> Yes(CheckSubject value) => Outcome<CheckSubject>.Success(value);
        if (condition.Operator is not CoreOperator op) return Yes(new());
        if (op.Operation == CoreOperation.Not) return Subject(c, condition.Operands[0], !positive, exception);
        // codegen/il2cpp-codegen-il2cpp.h: NullCheck、DivideByZeroCheck 比较对象或除数与零。
        if (exception is "System.NullReferenceException" or "System.DivideByZeroException" &&
            (op.Operation == CoreOperation.Equal && positive || op.Operation == CoreOperation.NotEqual && !positive))
        {
            var value = condition.Operands.FirstOrDefault(t => t.ConstantValue != 0);
            if (condition.Operands.Any(t => t.ConstantValue == 0) && value is not null) return Yes(new(Value: value));
        }
        // 同一头文件的 IL2CPP_ARRAY_BOUNDS_CHECK 使用无符号 index >= length。
        if (exception == "System.IndexOutOfRangeException" &&
            (op.Operation == CoreOperation.UnsignedLess && !positive || op.Operation == CoreOperation.UnsignedLessEqual && positive))
        {
            var index = condition.Operands[op.Operation == CoreOperation.UnsignedLess ? 0 : 1];
            var length = condition.Operands[op.Operation == CoreOperation.UnsignedLess ? 1 : 0]; Term? array = null;
            var memory = length.Identity as MemoryAtom;
            if (length.Kind == TermKind.Slice && length.SliceLow == 0) memory = length.Operands[0].Identity as MemoryAtom;
            if (memory is not null)
            {
                var loc = memory.Location; var address = loc.UnknownOffsetAddress;
                if (loc.Offset is { } offset) address = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), loc.Root.Width, loc.Root,
                    c.Snapshot.Terms.Constant(offset & ((System.Numerics.BigInteger.One << loc.Root.Width) - 1), loc.Root.Width));
                if (address is not null)
                {
                    var view = c.Get(q.Locations, new(address, length.Width)); if (!view.IsSuccess) return view.Propagate<CheckSubject>();
                    array = view.Value.Views.FirstOrDefault(v => v.Kind == ManagedLocationKind.ArrayLength)?.Root;
                }
            }
            return Yes(new(Index: index, Length: length, Array: array));
        }
        return Yes(new());
    }
}
