using System.Reflection;
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

public sealed record ClassInitializationAbsorption(TypeRef? Type, bool CanAbsorb, Reason? Why);
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
    public ClassInitializationQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names, ManagedLocationQuery locations, RuntimeSpec spec)
    {
        this.state = state; this.calls = calls; this.names = names; this.locations = locations; this.spec = spec;
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
        Outcome<ClassInitializationAbsorption> No(TypeRef? ownerType, string code, string message) =>
            Outcome<ClassInitializationAbsorption>.Success(new(ownerType, false, new("structure.class-init." + code, message)));
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
        if (init.Unwind is not null || init.DoesNotReturn)
            return No(type, "exception-region", "初始化带异常出口或不返回结局。");
        var result = c.Get(frontier, new(new(block.Identity, index + 1)));
        if (!result.IsSuccess) return result.Propagate<ClassInitializationAbsorption>();
        if (result.Value.HasCycle) return No(type, "cycle", "匹配访问前可能进入循环。");
        if (result.Value.ReachesExit || result.Value.Stops.Count == 0) return No(type, "exit", "有路径在匹配访问前退出。");
        foreach (var point in result.Value.Stops)
        {
            var reached = c.Get(points, point); if (!reached.IsSuccess) return reached.Propagate<ClassInitializationAbsorption>();
            if (reached.Value.Type != type) return No(type, "frontier", "初始化后先遇到" + Describe(c, point) + "，没有同类触发访问凭据。");
        }
        return Outcome<ClassInitializationAbsorption>.Success(new(type, true, null));
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
                if (call.Unwind is not null || call.DoesNotReturn) return Yes(true);
                if (named.Value.Operation is { Observation: RuntimeObservation.Unobservable }) return Yes(false);
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
