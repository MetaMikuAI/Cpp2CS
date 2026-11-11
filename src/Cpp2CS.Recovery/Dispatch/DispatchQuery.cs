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

public enum DispatchKind { Virtual, Delegate, Interface, Unresolved }
public enum TargetShape { VtableSlot, ManagedField, MemoryMerge, ValueMerge, CallResult, ReadFromValueMerge, ReadFromCallResult, IndexedMemoryRead, MemoryRead, Other }
/// <summary>Binding 保留原生实参（委托的 this 是 method_code）；托管调用接收者始终取 Receiver。</summary>
public sealed record DispatchResult(DispatchKind Kind, TargetShape Shape, Term? Receiver = null,
    TypeRef? StaticType = null, long? Slot = null, MethodRef? Method = null, BoundCall? Binding = null,
    ValueName? Evidence = null, Reason? Why = null, LocationView? FieldEvidence = null);

/// <summary>函数级只读分派查询；上下文由 Locations.CreateContext 建立。</summary>
/// <remarks>
/// 虚调用依据：生成代码 VirtualFuncInvoker / VirtualActionInvoker；
/// codegen/il2cpp-codegen-il2cpp.h::il2cpp_codegen_get_virtual_invoke_data；
/// il2cpp-class-internals.h::VirtualInvokeData。
/// 委托依据：生成代码 Invoke 内联体与 Multicast 桩；
/// il2cpp-object-internals.h::Il2CppDelegate；vm/Type.cpp::SetClosedDelegateInvokeMethod。
/// 接口快慢路径见 vm/ClassInlines.h/.cpp::GetInterfaceInvokeDataFromVTable。
/// </remarks>
public sealed class DispatchQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names,
    ManagedLocationQuery locations, MethodBinder binder, RuntimeSpec spec) : Query<CallIdentity, DispatchResult>
{
    private readonly InterfaceDataQuery interfaceData = new(state, calls, names, spec);
    public override Outcome<DispatchResult> Compute(QueryContext c, CallIdentity key)
    {
        var classified = c.Get(calls, key);
        if (!classified.IsSuccess) return classified.Propagate<DispatchResult>();
        if (classified.Value.Target is not { } target) return No(TargetShape.Other, "not-indirect", "调用目标不是计算值。");
        var resolved = c.Get(state.Resolve, target);
        if (!resolved.IsSuccess) return resolved.Propagate<DispatchResult>();
        target = resolved.Value;
        var named = c.Get(names, target);
        var site = c.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))))
            .Single(x => x.Statement is Call candidate && candidate.Identity == key);
        var call = (Call)site.Statement;
        if (named.IsSuccess && named.Value.Name is FieldName pointer &&
            pointer.Field == spec.Layout.Field("VirtualInvokeData", "methodPtr").Path &&
            pointer.Owner is FieldName { Record: "Il2CppClass", Field: "vtable", Index: { } slot } table &&
            table.Owner is FieldName klass && klass.Field == spec.Layout.Field("Il2CppObject", "klass").Path)
        {
            // 名字证明规格身份，状态项证明接收者身份；不以类型相同替代对象相同。
            if (target.Identity is not MemoryAtom pm || Resolve(c, pm.Location.Root)?.Identity is not MemoryAtom cm)
                return No(TargetShape.VtableSlot, "receiver-evidence", "虚表读取没有可追溯的对象项。");
            var receiver = Resolve(c, cm.Location.Root);
            if (receiver is null) return No(TargetShape.VtableSlot, "receiver-evidence", "对象项未解析。");
            var typed = c.Get(locations.Types, receiver);
            if (!typed.IsSuccess || typed.Value?.Type is not DefinitionRef type)
                return No(TargetShape.VtableSlot, "static-type", "接收者没有具体静态类型。", typed.Why);
            if (type.Definition.IsInterface) return No(TargetShape.VtableSlot, "interface-type", "接收者静态类型为接口。");
            if (Open(type)) return No(TargetShape.VtableSlot, "open-type", "开放类型不解析虚调用。");
            var method = SlotMethod(type, slot);
            if (method is null) return No(TargetShape.VtableSlot, "slot-method", "静态类型及基类没有唯一的槽方法。");
            if (method.Method.GenericParameters.Count != 0) return No(TargetShape.VtableSlot, "generic-method", "泛型虚方法不在本查询范围内。");
            var bound = binder.Call(call, method, BindingEntryKind.Ordinary, c.Snapshot.Terms);
            if (bound.Value is not { } binding) return No(TargetShape.VtableSlot, "binding", bound.Failure!.Detail);
            if (Value(c, binding.This, site.Point) != receiver) return No(TargetShape.VtableSlot, "receiver-mismatch", "首参不是虚表所属对象。");
            var info = Value(c, binding.MethodInformation, site.Point);
            Outcome<NamedValue>? infoName = info is null ? null : c.Get(names, info);
            if (infoName is not { IsSuccess: true } || infoName.Value.Value.Name is not FieldName mf ||
                mf.Field != spec.Layout.Field("VirtualInvokeData", "method").Path || mf.Owner != table ||
                info?.Identity is not MemoryAtom im || Resolve(c, im.Location.Root) != Resolve(c, pm.Location.Root))
                return No(TargetShape.VtableSlot, "method-information", "隐藏方法信息与目标不是同一对象的同一槽。");
            return Yes(new(DispatchKind.Virtual, TargetShape.VtableSlot, receiver, type, slot, method, binding, pointer));
        }
        var field = Field(c, target);
        if (field is not null && DelegateField(field, "invoke_impl"))
        {
            var receiver = Resolve(c, field.Root);
            if (receiver is null) return No(TargetShape.ManagedField, "delegate-type", "委托项未解析。");
            var typed = c.Get(locations.Types, receiver);
            if (!typed.IsSuccess || typed.Value?.Type is not DefinitionRef type || Open(type) ||
                type.Definition.BaseType is not DefinitionRef { Definition.Assembly: "mscorlib.dll", Definition.FullName: "System.MulticastDelegate" })
                return No(TargetShape.ManagedField, "delegate-type", "静态类型不是具体委托类型。");
            var methods = type.Definition.Methods.Where(m => m.Name == "Invoke" && !m.IsStatic).ToArray();
            if (methods.Length != 1) return No(TargetShape.ManagedField, "delegate-invoke", "委托类型没有唯一 Invoke。");
            var method = new MethodRef(methods[0], type.Arguments, []);
            var bound = binder.Call(call, method, BindingEntryKind.Ordinary, c.Snapshot.Terms);
            if (bound.Value is not { } binding) return No(TargetShape.ManagedField, "binding", bound.Failure!.Detail);
            // 生成的 Invoke 内联体：invoke_impl(method_code, 参数..., method)。
            // il2cpp-object-internals.h 的 invoke_impl_this 对应托管 method_code，不是 m_target。
            var self = Value(c, binding.This, site.Point); var info = Value(c, binding.MethodInformation, site.Point);
            if (self is null || Field(c, self) is not { } sf || !DelegateField(sf, "method_code") || Resolve(c, sf.Root) != receiver)
                return No(TargetShape.ManagedField, "delegate-this", "首参不是同一委托的 method_code。");
            if (info is null || Field(c, info) is not { } inf || !DelegateField(inf, "method") || Resolve(c, inf.Root) != receiver)
                return No(TargetShape.ManagedField, "delegate-method", "隐藏方法信息不是同一委托的 method。");
            return Yes(new(DispatchKind.Delegate, TargetShape.ManagedField, receiver, type, null, method, binding, FieldEvidence: field));
        }
        var shape = field is not null ? TargetShape.ManagedField : target.Identity switch
        {
            MemoryMerge => TargetShape.MemoryMerge,
            ResultAtom { Definition: MergeIdentity } => TargetShape.ValueMerge,
            ResultAtom { Definition: CallIdentity } => TargetShape.CallResult,
            MemoryAtom { Location.Root.Identity: ResultAtom { Definition: MergeIdentity } } => TargetShape.ReadFromValueMerge,
            MemoryAtom { Location.Root.Identity: ResultAtom { Definition: CallIdentity } } => TargetShape.ReadFromCallResult,
            MemoryAtom { Location.Offset: null } => TargetShape.IndexedMemoryRead,
            MemoryAtom => TargetShape.MemoryRead, _ => TargetShape.Other
        };
        var data = c.Get(interfaceData, new(target, site.Point, "methodPtr"));
        if (!data.IsSuccess) return Yes(new(DispatchKind.Unresolved, shape, Why: data.Why));
        var interfaceName = c.Get(names, data.Value.Interface);
        if (!interfaceName.IsSuccess || interfaceName.Value.Name is not EntityName { Entity: ClassEntity { Type: DefinitionRef interfaceType } } || !interfaceType.Definition.IsInterface || Open(interfaceType))
            return No(shape, "interface-name", "接口没有具体的元数据类型名字。");
        var interfaceMethods = interfaceType.Definition.Methods.Where(m => m.Slot == data.Value.Slot && !m.IsStatic).ToArray();
        if (interfaceMethods.Length != 1) return No(shape, "interface-slot-method", "接口槽号没有唯一方法。");
        if (interfaceMethods[0].GenericParameters.Count != 0) return No(shape, "interface-generic-method", "泛型接口方法不在查询范围内。");
        var interfaceMethod = new MethodRef(interfaceMethods[0], interfaceType.Arguments, []);
        var interfaceBound = binder.Call(call, interfaceMethod, BindingEntryKind.Ordinary, c.Snapshot.Terms);
        if (interfaceBound.Value is not { } interfaceBinding) return No(shape, "interface-binding", interfaceBound.Failure!.Detail);
        if (Value(c, interfaceBinding.This, site.Point) != data.Value.Object) return No(shape, "interface-receiver", "接收者不是调用数据所属对象。");
        var information = Value(c, interfaceBinding.MethodInformation, site.Point);
        if (information is null) return No(shape, "interface-method-information", "隐藏方法信息未绑定。");
        var infoData = c.Get(interfaceData, new(information, site.Point, "method"));
        if (!infoData.IsSuccess || !interfaceData.Same(c, data.Value, infoData.Value))
            return No(shape, "interface-method-information", "目标与隐藏方法信息不是同一接口调用数据。", infoData.Why);
        return Yes(new(DispatchKind.Interface, shape, data.Value.Object, interfaceType, data.Value.Slot, interfaceMethod, interfaceBinding, data.Value));
    }
    private static bool Open(DefinitionRef type) => type.Definition.GenericParameters.Count != type.Arguments.Count || type.ContainsGenericParameter();
    private static MethodRef? SlotMethod(DefinitionRef type, long slot)
    {
        for (DefinitionRef? current = type; current is not null; current = current.Definition.BaseType?.Substitute(current.Arguments, []) as DefinitionRef)
        {
            var matches = current.Definition.Methods.Where(m => m.Slot == slot && m.IsVirtual && !m.IsStatic).ToArray();
            if (matches.Length > 1) return null;
            if (matches.Length == 1)
            {
                var result = new MethodRef(matches[0], current.Arguments, []);
                if (type.Definition.VTable.Count > 0)
                {
                    if (slot < 0 || slot >= type.Definition.VTable.Count || type.Definition.VTable[(int)slot] is not { } actual) return null;
                    var concrete = new MethodRef(actual.Method, actual.TypeArguments.Select(t => t.Substitute(type.Arguments, [])).ToArray(), actual.MethodArguments);
                    if (result != concrete) return null;
                }
                return result;
            }
        }
        return null;
    }
    private Term? Resolve(QueryContext c, Term term) { var r = c.Get(state.Resolve, term); return r.IsSuccess ? r.Value : null; }
    private Term? Value(QueryContext c, BoundValue? value, Point point)
    {
        if (value?.Source is TermSource term) return Resolve(c, term.Term);
        if (value?.Source is not PiecesSource { Pieces.Length: 1 } pieces || pieces.Pieces[0] is not
            { ValueOffset: 0, Source: StackSource stack } || stack.Length != value.Type.Size) return null;
        var area = Resolve(c, stack.Area);
        if (area is null) return null;
        var terms = c.Snapshot.Terms;
        var address = terms.Apply(new CoreOperator(CoreOperation.Add), area.Width, area, terms.Constant(stack.Offset, area.Width));
        var location = c.Get(state.Locations, new(address, stack.Length * 8));
        if (!location.IsSuccess) return null;
        var content = c.Get(state.ValueAt, new(point, location.Value));
        return content.IsSuccess ? Resolve(c, content.Value) : null;
    }
    private LocationView? Field(QueryContext c, Term term)
    {
        if (term.Identity is not MemoryAtom m || m.Location.Offset is not { } offset) return null;
        var t = c.Snapshot.Terms;
        var address = t.Apply(new CoreOperator(CoreOperation.Add), m.Location.Root.Width, m.Location.Root,
            t.Constant(offset & ((System.Numerics.BigInteger.One << m.Location.Root.Width) - 1), m.Location.Root.Width));
        var found = c.Get(locations, new(address, m.Location.Width));
        if (!found.IsSuccess) return null;
        var fields = found.Value.Views.Where(v => v.Kind == ManagedLocationKind.InstanceField && v.Offset == 0 && v.Path.Length == 1 && v.Width == c.Snapshot.AddressWidth).ToArray();
        return fields.Length == 1 ? fields[0] : null;
    }
    private static bool DelegateField(LocationView view, string name) => view.Path[0].Field is
        { Owner.Assembly: "mscorlib.dll", Owner.FullName: "System.Delegate" } field && field.Name == name;
    private static Outcome<DispatchResult> Yes(DispatchResult result) => Outcome<DispatchResult>.Success(result);
    private static Outcome<DispatchResult> No(TargetShape shape, string code, string detail, Reason? cause = null)
        => Yes(new(DispatchKind.Unresolved, shape, Why: new("dispatch." + code, detail, cause)));
}
