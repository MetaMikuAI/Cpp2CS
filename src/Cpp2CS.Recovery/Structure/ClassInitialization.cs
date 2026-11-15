using System.Reflection;
using System.Collections.Immutable;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Structure;

public sealed record ClassInitializationAbsorption(TypeRef? Type, bool CanAbsorb, Reason? Why)
{
    /// <summary>吸收后仍须保留展开归属的内存访问；入口为空表示向外传播。</summary>
    public ImmutableArray<StableIdentity> ProtectedAccesses { get; init; } = [];
    public BlockIdentity? Handler { get; init; }
}
internal sealed record InitializationPoint(bool Stop, TypeRef? Type);

/// <summary>精确初始化只能移入每条路径首先遇到的同类访问；退出、循环及其他观察均阻止吸收。</summary>
public sealed class ClassInitializationQuery : Query<CallIdentity, ClassInitializationAbsorption>
{
    private readonly StateQueries state;
    private readonly CallNamingQuery calls;
    private readonly ValueNamingQuery names;
    private readonly ManagedLocationQuery locations;
    private readonly RuntimeSpec spec;
    private readonly ManagedCallAddressQuery addresses;
    private readonly InitializationPointQuery points;
    private readonly EventFrontierQuery frontier;
    private readonly ExceptionRegionQuery? regions;
    public ClassInitializationQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names, ManagedLocationQuery locations, RuntimeSpec spec, ExceptionRegionQuery? regions = null)
    {
        this.state = state; this.calls = calls; this.names = names; this.locations = locations; this.spec = spec;
        this.regions = regions;
        addresses = new(state, calls, locations);
        points = new(this);
        frontier = new((c, p) =>
        {
            var point = c.Get(points, p);
            return point.IsSuccess ? Outcome<bool>.Success(point.Value.Stop) : point.Propagate<bool>();
        });
    }
    public override Outcome<ClassInitializationAbsorption> Compute(QueryContext c, CallIdentity key)
    {
        var named = c.Get(calls, key); if (!named.IsSuccess) return named.Propagate<ClassInitializationAbsorption>();
        Outcome<ClassInitializationAbsorption> No(TypeRef? ownerType, string code, string message, Reason? cause = null) =>
            Outcome<ClassInitializationAbsorption>.Success(new(ownerType, false, new("structure.class-init." + code, message, cause)));
        if (named.Value.Operation is not { RelaxedClassInput: { } input, Observation: RuntimeObservation.IdempotentEvent,
            Result.Kind: RuntimeValueKind.Void } || named.Value.Inputs?.GetValueOrDefault(input)?.Source is not TermSource source)
            return No(null, "operation", "调用不是已绑定的精确类初始化。");
        var owner = c.Get(names, source.Term); if (!owner.IsSuccess) return owner.Propagate<ClassInitializationAbsorption>();
        if (owner.Value.Name is not EntityName { Entity: ClassEntity { Type: { } type } })
            return No(null, "owner", "初始化类没有实体凭据。");
        var block = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(call => call.Identity == key));
        int index = 0;
        while (block.Statements[index] is not Call found || found.Identity != key) index++;
        var init = (Call)block.Statements[index];
        if (init.DoesNotReturn)
            return No(type, "exception-region", "初始化带不返回结局。");
        var result = c.Get(frontier, new(new(block.Identity, index + 1)));
        if (!result.IsSuccess) return result.Propagate<ClassInitializationAbsorption>();
        if (result.Value.HasCycle) return No(type, "cycle", "匹配访问前可能进入循环。");
        if (result.Value.ReachesExit || result.Value.Stops.Count == 0) return No(type, "exit", "有路径在匹配访问前退出。");
        var protectedAccesses = ImmutableArray.CreateBuilder<StableIdentity>();
        BlockIdentity? memoryHandler = null;
        foreach (var point in result.Value.Stops)
        {
            var reached = c.Get(points, point); if (!reached.IsSuccess) return reached.Propagate<ClassInitializationAbsorption>();
            if (reached.Value.Type != type) return No(type, "frontier", "初始化后先遇到" + Describe(c, point) + "，没有同类触发访问凭据。");
            var statement = c.Snapshot.Blocks.Single(b => b.Identity == point.Block).Statements[point.Before];
            var target = UnwindAt(c, point);
            // 区域计划会略去只执行 C++ 私有操作的透明清理；内存访问与初始化沿用同一计划的逻辑入口。
            var initialTarget = statement is Call ? Outcome<BlockIdentity?>.Success(init.Unwind)
                : UnwindAt(c, new(block.Identity, index), logicalCall: true);
            if (statement is Call && target.IsSuccess && target.Value != init.Unwind && regions is not null)
            {
                target = UnwindAt(c, point, logicalCall: true);
                initialTarget = UnwindAt(c, new(block.Identity, index), logicalCall: true);
            }
            if (!target.IsSuccess || !initialTarget.IsSuccess)
                return No(type, "exception-region", "吸收访问的受保护区域不可判定。", target.Why ?? initialTarget.Why);
            if (target.Value != initialTarget.Value) return No(type, "exception-region", "初始化与同类触发访问的展开目标不同。");
            if (target.Value is not null || regions is not null)
            {
                if (statement is MemoryRead read) { protectedAccesses.Add(read.Identity); memoryHandler = target.Value; }
                if (statement is MemoryWrite write) { protectedAccesses.Add(write.Identity); memoryHandler = target.Value; }
            }
        }
        return Outcome<ClassInitializationAbsorption>.Success(new(type, true, null)
        { ProtectedAccesses = protectedAccesses.ToImmutable(), Handler = memoryHandler });
    }
    /// <summary>调用取显式展开边；内存访问取现有区域查询给出的最内层 try。</summary>
    private Outcome<BlockIdentity?> UnwindAt(QueryContext c, Point point, bool logicalCall = false)
    {
        var block = c.Snapshot.Blocks.Single(b => b.Identity == point.Block);
        var call = block.Statements[point.Before] as Call;
        if (call is not null && !logicalCall) return Outcome<BlockIdentity?>.Success(call.Unwind);
        bool hasHandlers = c.Snapshot.Blocks.Any(b => b.Handler is not null);
        if (call is not null && (call.Unwind is null || !hasHandlers)) return Outcome<BlockIdentity?>.Success(call.Unwind);
        if (!hasHandlers) return Outcome<BlockIdentity?>.Success(null);
        if (regions is null) return Outcome<BlockIdentity?>.Failure(new("structure.class-init.exception-region", "缺少受保护区域查询。"));
        var plan = c.Get(regions, 0);
        if (!plan.IsSuccess) return plan.Propagate<BlockIdentity?>();
        if (call is null && plan.Value.Removed.Contains(point.Block))
            return Outcome<BlockIdentity?>.Failure(new("structure.class-init.exception-region", "同类内存访问位于异常计划略去的私有块中。"));
        return Outcome<BlockIdentity?>.Success(call is not null ? plan.Value.Unwind[call.Identity] : plan.Value.Regions
            .Where(r => r.Try.Contains(point.Block)).OrderBy(r => r.Try.Count).Select(r => r.Source).FirstOrDefault());
    }

    /// <summary>删除调用后，内存访问不能丢失原来的保护；原生读取本身不携带展开边。</summary>
    public bool PreservesProtection(QueryContext c, IEnumerable<ClassInitializationAbsorption> absorptions)
    {
        foreach (var absorption in absorptions)
        foreach (var access in absorption.ProtectedAccesses)
        {
            var points = c.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))));
            var found = points.FirstOrDefault(p => p.Statement is MemoryRead read && read.Identity == access
                || p.Statement is MemoryWrite write && write.Identity == access);
            if (found.Statement is null || UnwindAt(c, found.Point) is not { IsSuccess: true } target || target.Value != absorption.Handler) return false;
        }
        return true;
    }
    private string Describe(QueryContext c, Point point)
    {
        var block = c.Snapshot.Blocks.Single(b => b.Identity == point.Block);
        if (point.Before == block.Statements.Length) return "结局";
        var statement = block.Statements[point.Before];
        if (statement is Call call && c.Get(calls, call.Identity) is { IsSuccess: true } named)
            return "调用 " + (named.Value.Operation?.Name ?? named.Value.Candidates?.Candidates.FirstOrDefault()?.Entry.Method?.ToString() ?? named.Value.Kind.ToString());
        return statement switch { MemoryRead => "读取", MemoryWrite => "写入", _ => statement.GetType().Name }
            + (statement.Trace?.NativeAddress is { } address ? $"（0x{address:x}）" : "");
    }
    private sealed class InitializationPointQuery(ClassInitializationQuery q) : Query<Point, InitializationPoint>
    {
        public override Outcome<InitializationPoint> Compute(QueryContext c, Point key)
        {
            var indexed = c.Get(q.state.Index, 0); if (!indexed.IsSuccess) return indexed.Propagate<InitializationPoint>();
            var b = indexed.Value.Blocks[key.Block];
            Outcome<InitializationPoint> Yes(bool stop, TypeRef? type = null) => Outcome<InitializationPoint>.Success(new(stop, type));
            if (key.Before == b.Statements.Length) return Yes(false);
            var statement = b.Statements[key.Before];
            if (statement is Call call)
            {
                var named = c.Get(q.calls, call.Identity); if (!named.IsSuccess) return named.Propagate<InitializationPoint>();
                if (call.DoesNotReturn) return Yes(true);
                if (named.Value.Operation is { Observation: RuntimeObservation.Unobservable }) return Yes(call.Unwind is not null);
                // Object::NewAllocSpecific 在返回新对象前运行同类静态构造；下降另行复核 newobj 配对。
                if (named.Value.Operation is { Il.Name: "NewObject" } && named.Value.Inputs?.GetValueOrDefault("class")?.Source is TermSource allocated
                    && c.Get(q.names, allocated.Term) is { IsSuccess: true, Value.Name: EntityName { Entity: ClassEntity allocation } })
                    return Yes(true, allocation.Type);
                var addresses = c.Get(q.addresses, call.Identity); if (!addresses.IsSuccess) return addresses.Propagate<InitializationPoint>();
                if (!addresses.Value.IsEmpty && addresses.Value.All(v => v.Kind == ManagedLocationKind.StaticField))
                {
                    var owners = addresses.Value.Select(v => v.Path[0].DeclaringType).Distinct().ToArray();
                    if (owners is [var owner]) return Yes(true, owner);
                }
                if (named.Value.Kind == CallKind.Managed && named.Value.Candidates is { Failure: null, Candidates.Length: > 0 } candidates)
                {
                    TypeRef? common = null;
                    foreach (var candidate in candidates.Candidates)
                    {
                        if (!candidate.Binding.Success || candidate.Entry.Kind != BindingEntryKind.Ordinary ||
                            candidate.Entry.Method is not { } method ||
                            (!method.Method.IsStatic && !(method.Method.Name == ".ctor" &&
                                (method.Method.Attributes & (MethodAttributes.SpecialName | MethodAttributes.RTSpecialName)) ==
                                (MethodAttributes.SpecialName | MethodAttributes.RTSpecialName))) || method.Method.Name == ".cctor") return Yes(true);
                        if (common is not null && common != method.DeclaringType) return Yes(true);
                        common = method.DeclaringType;
                    }
                    return Yes(true, common);
                }
                return Yes(true);
            }
            var request = statement switch
            { MemoryRead read => new AddressRequest(read.Address, read.Width), MemoryWrite write => new AddressRequest(write.Address, write.Width), _ => default };
            if (request.Address is null) return Yes(true);
            var nativeAddress = c.Get(q.state.Resolve, request.Address); if (!nativeAddress.IsSuccess) return nativeAddress.Propagate<InitializationPoint>();
            var native = c.Get(q.state.Locations, new(nativeAddress.Value, request.Width)); if (!native.IsSuccess) return native.Propagate<InitializationPoint>();
            if (native.Value.Region == Region.Frame)
            {
                var escaped = c.Get(q.state.Escapes, 0); if (!escaped.IsSuccess) return escaped.Propagate<InitializationPoint>();
                return Yes(escaped.Value.MayReach(native.Value));
            }
            var located = c.Get(q.locations, request); if (!located.IsSuccess) return located.Propagate<InitializationPoint>();
            if (located.Value.Kind == ManagedLocationKind.NotManaged)
            {
                if (statement is not MemoryRead read) return Yes(true);
                var named = c.Get(q.names, read.Result); if (!named.IsSuccess) return named.Propagate<InitializationPoint>();
                // 元数据实体与静态字段块地址不随静态构造改变；状态标志等其余读取保留为屏障。
                return Yes(named.Value.Name is not EntityName && !(named.Value.Name is FieldName field &&
                    field.Field == q.spec.Layout.Field("Il2CppClass", "static_fields").Path));
            }
            if (located.Value.Kind != ManagedLocationKind.StaticField || located.Value.Views.IsEmpty) return Yes(true);
            var types = located.Value.Views.Select(v => v.Path.IsEmpty ? null : v.Path[0].DeclaringType).Distinct().ToArray();
            return Yes(true, types is [var type] ? type : null);
        }
    }
}
