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

namespace Cpp2CS.Recovery.Dispatch;

public sealed partial class DispatchQuery
{
    private readonly StridedAddressQuery genericStrides = new(state);

    private Outcome<DispatchResult>? GenericVirtual(QueryContext c, Call call, Term target, Point point)
    {
        var pointer = c.Get(reads, target);
        if (!pointer.IsSuccess || pointer.Value.Width != c.Snapshot.AddressWidth
            || pointer.Value.Offset != spec.Layout.Field("MethodInfo", "virtualMethodPointer").ByteOffset) return null;
        var root = Resolve(c, pointer.Value.Root);
        if (root?.Identity is not ResultAtom { Definition: CallIdentity resolverId }
            || c.Get(calls, resolverId) is not { IsSuccess: true, Value.Operation.Name: "ResolveGenericVirtual" } resolved) return null;
        Outcome<DispatchResult> Missing(string code, string text, Reason? cause = null) => Yes(new(DispatchKind.Unresolved, TargetShape.ReadFromCallResult,
            Why: new("dispatch.generic-" + code, text, cause)) { GenericResolution = resolverId });
        var operation = resolved.Value;
        if (operation.Inputs?.GetValueOrDefault("method")?.Source is not TermSource methodInput
            || c.Get(names, methodInput.Term) is not { IsSuccess: true, Value.Name: EntityName { Entity: MethodEntity entity } })
            return Missing("method", "泛型虚解析的方法信息不是已命名的方法实体。");
        var method = entity.Method;
        if (!method.Method.IsVirtual || method.Method.IsStatic || method.Method.GenericParameters.Count == 0
            || method.Method.Slot is < 0 or > ushort.MaxValue
            || method.MethodArguments.Count != method.Method.GenericParameters.Count || method.TypeArguments.Count != method.Method.Owner.GenericParameters.Count)
            return Missing("method", "方法实体不是完整实例化的泛型虚方法。");
        if (operation.Inputs?.GetValueOrDefault("definition")?.Source is not TermSource definition
            || operation.Result?.Source is not TermSource output || !Same(c, output.Term, root))
            return Missing("binding", "泛型虚解析没有完整绑定的方法定义或结果。");
        Term? receiver = null;
        var definitionRead = c.Get(reads, definition.Term);
        if (!method.Method.Owner.IsInterface && definitionRead.IsSuccess)
        {
            var location = definitionRead.Value;
            var address = Address(c, location);
            var memberOffset = spec.Layout.VtableStart + spec.Layout.Field("VirtualInvokeData", "method").ByteOffset;
            var stride = c.Get(genericStrides, new(address, spec.Layout.VtableSlotSize));
            if (stride.IsSuccess && c.Get(names, stride.Value.Base) is
                { IsSuccess: true, Value.Name: FieldName { Field: "Il2CppObject.klass" } }
                && c.Get(reads, stride.Value.Base) is { IsSuccess: true } objectClass)
            {
                var terms = c.Snapshot.Terms;
                Term Add(Term a, Term b) => terms.Apply(new CoreOperator(CoreOperation.Add), a.Width, a, b);
                var constantSlot = Add(stride.Value.Base, terms.Constant(memberOffset + method.Method.Slot * spec.Layout.VtableSlotSize, address.Width));
                bool slotMatches = Same(c, address, constantSlot);
                // 动态槽仍是 MethodInfo.slot；下标完整等于此读取，不能只凭模步长视图猜槽。
                foreach (var slot in SnapshotRewrite.Dependencies([address]))
                {
                    if (c.Get(names, slot) is not { IsSuccess: true, Value.Name: FieldName { Field: "MethodInfo.slot", Owner: EntityName { Entity: MethodEntity slotMethod } } }
                        || slotMethod.Method != method) continue;
                    var extended = slot.Width == address.Width ? slot : terms.Apply(new CoreOperator(CoreOperation.ZeroExtend), address.Width, slot);
                    var index = terms.Apply(new CoreOperator(CoreOperation.Multiply), address.Width, extended, terms.Constant(spec.Layout.VtableSlotSize, address.Width));
                    var expected = Add(Add(stride.Value.Base, index), terms.Constant(memberOffset, address.Width));
                    slotMatches |= Same(c, address, expected);
                }
                if (slotMatches) receiver = Resolve(c, objectClass.Value.Root);
            }
        }
        else if (method.Method.Owner.IsInterface)
        {
            var data = c.Get(interfaceData, new(definition.Term, point, "method"));
            if (data.IsSuccess && !InterfaceDataQuery.IsPending(data.Value) && data.Value.Slot == method.Method.Slot
                && c.Get(names, data.Value.Interface) is { IsSuccess: true, Value.Name: EntityName { Entity: ClassEntity itf } }
                && itf.Type == method.DeclaringType) receiver = data.Value.Object;
        }
        if (receiver is null) return Missing("receiver", "方法定义没有同一对象及同一方法槽的虚表或接口调用数据凭据。");
        var nativeMethod = method;
        if (method.TypeArguments.Concat(method.MethodArguments).Any(t => t.ContainsGenericParameter()))
        {
            if (witness is null || !witness.Knows(method)) return Missing("context", "泛型虚方法的开放实参不属于当前泛型见证。");
            nativeMethod = witness.Close(method);
        }
        var bound = binder.Call(call, nativeMethod, BindingEntryKind.Ordinary, c.Snapshot.Terms);
        if (bound.Value is not { } binding) return Missing("binding", bound.Failure!.Detail);
        binding = binding with { Signature = binding.Signature with { Entry = new(method, BindingEntryKind.Ordinary) } };
        if (Value(c, binding.This, point) is not { } self || !Same(c, self, receiver)) return Missing("receiver", "间接调用的接收者与解析方法定义的对象不同。");
        if (Value(c, binding.MethodInformation, point) is not { } info || !Same(c, info, root))
            return Missing("information", "隐藏方法信息不是同一次泛型虚解析的结果。");
        var source = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == resolverId));
        int at = 0; while (source.Statements[at] is not Call found || found.Identity != resolverId) at++;
        var resolver = (Call)source.Statements[at];
        if (resolver.Unwind is not null || call.Unwind is not null) return Missing("unwind", "解析与间接调用带异常出口，尚未证明合并后的异常状态。");
        var frontier = new EventFrontierQuery((context, where) =>
        {
            var owner = context.Snapshot.Blocks.Single(b => b.Identity == where.Block);
            if (where.Before == owner.Statements.Length) return Outcome<bool>.Success(false);
            var statement = owner.Statements[where.Before];
            if (statement is Call called)
                return context.Get(calls, called.Identity) is { IsSuccess: true } named
                    ? Outcome<bool>.Success(named.Value.Operation is not { Observation: RuntimeObservation.Unobservable })
                    : Outcome<bool>.Success(true);
            if (statement is MemoryRead read)
            {
                // 目标读取来自已复核的解析结果，不要求该私有方法指针跨版本不变。
                if (Same(context, read.Result, target)) return Outcome<bool>.Success(false);
                var address = context.Get(state.Resolve, read.Address);
                var location = address.IsSuccess ? context.Get(state.Locations, new(address.Value, read.Width)) : default;
                var fixedValue = names.FixedValue(context, read.Result);
                return Outcome<bool>.Success(!(location.IsSuccess && location.Value.Region == Region.Frame)
                    && fixedValue is not { IsSuccess: true, Value: EntityName or FieldName or ArrayElementName });
            }
            return Outcome<bool>.Success(true);
        });
        var next = c.Get(frontier, new(new(source.Identity, at + 1)));
        if (!next.IsSuccess) return Missing("frontier", "解析后的事件前沿查询失败。", next.Why);
        if (next.Value.HasCycle || next.Value.ReachesExit || next.Value.Stops.Count != 1 || !next.Value.Stops.Contains(point))
            return Missing("frontier", "解析后没有在其他观察、退出或循环之前唯一到达该间接调用。");
        var pointerValues = c.Snapshot.Blocks.SelectMany(b => b.Statements).OfType<MemoryRead>()
            .Where(read => Same(c, read.Result, target)).Select(read => read.Result).ToHashSet();
        bool Uses(Term value)
        {
            var dependencies = SnapshotRewrite.Dependencies([value]);
            return dependencies.Contains(output.Term) || dependencies.Overlaps(pointerValues);
        }
        var sources = new BoundSourceQuery(state);
        foreach (var argument in binding.Parameters)
            if (c.Get(sources, new(argument.Source, point)) is { IsSuccess: true } value && Uses(value.Value))
                return Missing("uses", "解析结果或目标指针还被传作用户方法实参。");
        foreach (var owner in c.Snapshot.Blocks)
        {
            if (owner.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)).Concat(SnapshotRewrite.Uses(owner.End)).Any(Uses))
                return Missing("uses", "解析结果流入合流或终结，不能只由虚调用吸收。");
            foreach (var statement in owner.Statements)
            {
                if (ReferenceEquals(statement, call)) continue;
                if (statement is MemoryRead read && Same(c, read.Result, target)) continue;
                if (SnapshotRewrite.Uses(statement).Any(Uses)) return Missing("uses", "解析结果还有目标读取与单次调用以外的使用。");
            }
        }
        return Yes(new(method.Method.Owner.IsInterface ? DispatchKind.Interface : DispatchKind.Virtual,
            TargetShape.ReadFromCallResult, receiver, method.DeclaringType, method.Method.Slot, method, binding)
            { GenericResolution = resolverId });
    }
    private bool Same(QueryContext c, Term a, Term b) => names.SameValue(c, a, b) is { IsSuccess: true, Value: true };
    private static Term Address(QueryContext c, Location location) => location.UnknownOffsetAddress
        ?? c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.Add), location.Root.Width, location.Root,
            c.Snapshot.Terms.Constant(location.Offset!.Value & ((System.Numerics.BigInteger.One << location.Root.Width) - 1), location.Root.Width));
}
