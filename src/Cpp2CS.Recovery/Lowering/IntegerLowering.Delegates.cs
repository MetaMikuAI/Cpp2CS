using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private readonly HashSet<CallIdentity> methodLookups = [];
    private readonly Dictionary<CallIdentity, int> delegateLookups = [];

    /// <summary>仅消费现有对象创建查询配对成功的标准委托构造。</summary>
    private ManagedStatement? LowerDelegate(CallDefinition call, ObjectDefinition created, Point point)
    {
        if (created.Type is not DefinitionRef type || call.Method.Method.Parameters.Count != 2
            || !call.Method.Concrete(call.Method.Method.Parameters[0].Type).Equals(types.Object)
            || !call.Method.Concrete(call.Method.Method.Parameters[1].Type).Equals(types.IntPtr)
            || call.Binding.Parameters.Length != 2 || dispatch is null || valueNames is null)
            return Fail<ManagedStatement>(LoweringFailureKind.Call, "委托构造没有标准 (object, native int) 签名或方法身份查询。", code: "lowering.Delegate.Constructor");
        var targetTerm = BoundTerm(call.Binding.Parameters[0].Source, point);
        var information = BoundTerm(call.Binding.Parameters[1].Source, point);
        if (targetTerm is null || information is null) return null;
        var resolved = dispatch.MethodInformation(context, information, point);
        if (!resolved.IsSuccess) return Fail<ManagedStatement>(LoweringFailureKind.Call, "委托方法身份未解析。", resolved.Why, "lowering.Delegate.Method");
        var methodInfo = resolved.Value;
        if (methodInfo.Receiver is { } receiver)
        {
            var same = valueNames.SameValue(context, receiver, targetTerm);
            if (!same.IsSuccess || !same.Value)
                return Fail<ManagedStatement>(LoweringFailureKind.Call, "取槽位的对象与委托目标不是同一个值。", same.Why, "lowering.Delegate.Receiver");
        }
        if (methodInfo.Lookup is { } lookup)
        {
            if (!AdjacentMethodLookup(lookup, created, point)) return null;
            delegateLookups[lookup] = delegateLookups.GetValueOrDefault(lookup) + 1;
        }
        constructing = created;
        var target = CallArgument(call.Binding.Parameters[0], types.Object, point);
        constructing = null;
        if (target is null) return null;
        if (!ManagedAccess.Method(types, method.Method.Owner, call.Method, null))
            return Fail<ManagedStatement>(LoweringFailureKind.Call, "委托构造函数不可访问。", code: "lowering.Access.Method");
        var binding = methodInfo.Receiver is not null ? DelegateBinding.VirtualInstance
            : methodInfo.Method.Method.IsStatic ? DelegateBinding.Static : DelegateBinding.ClosedInstance;
        return new ManagedAssignment(position, created.Local!, new DelegateValue(type, target, methodInfo.Method, binding, types.PointerSize * 8));
    }

    /// <summary>查找的异常与效果只能移动到紧随其后的新分配；配对条件仍由对象创建查询负责。</summary>
    private bool AdjacentMethodLookup(CallIdentity lookup, ObjectDefinition created, Point construction)
    {
        var site = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))))
            .Single(s => s.Statement is Call call && call.Identity == lookup);
        var lookupCall = (Call)site.Statement;
        var constructorCall = (Call)function.Blocks.Single(b => b.Identity == construction.Block).Statements[construction.Before];
        if (lookupCall.Unwind != constructorCall.Unwind)
        {
            Fail<object>(LoweringFailureKind.Call, "方法查找与委托构造的异常续点不同。", code: "lowering.Delegate.LookupOrder"); return false;
        }
        var frontier = new EventFrontierQuery((c, point) =>
        {
            var block = function.Blocks.Single(b => b.Identity == point.Block);
            return Outcome<bool>.Success(point.Before < block.Statements.Length
                && !AllocationConstructorQuery.PrivateAccess(c, state, locations, block.Statements[point.Before]));
        });
        var reached = context.Get(frontier, new(new(site.Point.Block, site.Point.Before + 1)));
        if (reached.IsSuccess && !reached.Value.HasCycle && !reached.Value.ReachesExit && reached.Value.Stops.Count > 0
            && reached.Value.Stops.All(p => function.Blocks.Single(b => b.Identity == p.Block).Statements[p.Before] is Call call
                && allocations.TryGetValue(call.Identity, out var allocation) && allocation == created)) return true;
        Fail<object>(LoweringFailureKind.Call, "方法信息查找之后不是无托管访问的同一委托分配。", reached.Why, "lowering.Delegate.LookupOrder");
        return false;
    }
}
