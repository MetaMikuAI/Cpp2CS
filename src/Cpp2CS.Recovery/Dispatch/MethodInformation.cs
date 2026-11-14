using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Dispatch;

/// <summary>委托构造使用的方法身份；Receiver 非空表示按同一对象动态取槽。</summary>
public sealed record MethodInformationResult(MethodRef Method, Term? Receiver = null, CallIdentity? Lookup = null);

public sealed partial class DispatchQuery
{
    internal static bool IsDelegateType(TypeRef type) => type is DefinitionRef { Definition.BaseType: DefinitionRef
        { Definition.Assembly: "mscorlib.dll", Definition.FullName: "System.MulticastDelegate" } };

    /// <summary>直接实体沿用命名，动态方法信息沿用虚表与接口槽解析；不产生独立托管指针值。</summary>
    public Outcome<MethodInformationResult> MethodInformation(QueryContext c, Term value, Point point)
    {
        if (names.DispatchedCalls is { } shared && shared != this) return shared.MethodInformation(c, value, point);
        var resolved = c.Get(state.Resolve, value); if (!resolved.IsSuccess) return resolved.Propagate<MethodInformationResult>();
        value = resolved.Value;
        var fixedValue = names.FixedValue(c, value);
        if (fixedValue is { IsSuccess: true, Value: EntityName { Entity: MethodEntity entity } })
            return Outcome<MethodInformationResult>.Success(new(entity.Method));
        var named = c.Get(names, value);
        if (named is { IsSuccess: true, Value.Name: FieldName field }
            && field.Field == spec.Layout.Field("VirtualInvokeData", "method").Path
            && field.Owner is FieldName { Record: "Il2CppClass", Field: "vtable", Index: { } slot } table
            && table.Owner is FieldName klass && klass.Field == spec.Layout.Field("Il2CppObject", "klass").Path)
        {
            var informationRead = c.Get(reads, value);
            if (!informationRead.IsSuccess) return Missing("receiver-evidence", "虚表方法信息没有完整读取凭据。", informationRead.Why);
            var classRead = c.Get(reads, informationRead.Value.Root);
            if (!classRead.IsSuccess) return Missing("receiver-evidence", "虚表的类没有所属对象。", classRead.Why);
            return VirtualInformation(c, classRead.Value.Root, slot);
        }
        if (value.Identity is ResultAtom { Definition: CallIdentity lookup })
        {
            var classified = c.Get(calls, lookup);
            if (classified is { IsSuccess: true, Value.Operation.Name: "LookupVirtualMethod" or "LookupInterfaceMethod" })
            {
                if (classified.Value.Result?.Source is not TermSource output || Resolve(c, output.Term) != value)
                    return Missing("result", "方法查找实参不是已绑定的完整返回值。");
                var site = c.Snapshot.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Point: new Point(b.Identity, i))))
                    .Single(s => s.Statement is Call call && call.Identity == lookup);
                var sources = new BoundSourceQuery(state);
                Outcome<Term> Input(string input) => classified.Value.Inputs?.GetValueOrDefault(input) is { } bound
                    ? c.Get(sources, new(bound.Source, site.Point)) : Outcome<Term>.Failure(new("dispatch.method-input", "运行时方法查找的输入没有绑定。"));
                var obj = Input("object"); var index = Input("slot");
                if (!obj.IsSuccess) return obj.Propagate<MethodInformationResult>();
                if (!index.IsSuccess) return index.Propagate<MethodInformationResult>();
                var actual = Resolve(c, obj.Value); var number = Resolve(c, index.Value)?.ConstantValue;
                if (actual is null || number is null || number < 0 || number > ushort.MaxValue)
                    return Missing("slot", "方法查找的对象或常量槽号没有完整凭据。");
                if (classified.Value.Operation!.Name == "LookupVirtualMethod") return VirtualInformation(c, actual, (long)number, lookup);
                var itf = Input("interface"); if (!itf.IsSuccess) return itf.Propagate<MethodInformationResult>();
                return InterfaceInformation(c, new(actual, itf.Value, (long)number, "LookupInterfaceMethod"), lookup);
            }
        }
        var data = c.Get(interfaceData, new(value, point, "method"));
        if (data.IsSuccess && !InterfaceDataQuery.IsPending(data.Value))
        {
            var read = c.Get(reads, value);
            CallIdentity? dataLookup = read.IsSuccess && read.Value.Root.Identity is ResultAtom { Definition: CallIdentity source }
                && c.Get(calls, source) is { IsSuccess: true, Value.Operation.Name: "LookupInterfaceData" } ? source : null;
            return InterfaceInformation(c, data.Value, dataLookup);
        }
        var cause = named.IsSuccess ? named.Value.Why : named.Why;
        return Missing("source", "委托的方法实参既非方法实体，也非已解析的动态槽位。", cause ?? data.Why);
    }

    private Outcome<MethodInformationResult> VirtualInformation(QueryContext c, Term receiver, long slot, CallIdentity? lookup = null)
    {
        var typed = c.Get(locations.Types, receiver);
        if (!typed.IsSuccess || typed.Value?.Type is not DefinitionRef type || type.Definition.IsInterface || Open(type))
            return Missing("static-type", "取虚表方法信息的对象没有具体的类静态类型。", typed.Why);
        var method = SlotMethod(type, slot);
        return method is null || method.Method.GenericParameters.Count != 0
            ? Missing("slot-method", "对象静态类型及基类没有唯一的非泛型槽方法。")
            : Outcome<MethodInformationResult>.Success(new(method, receiver, lookup));
    }

    private Outcome<MethodInformationResult> InterfaceInformation(QueryContext c, InterfaceDataName data, CallIdentity? lookup = null)
    {
        var method = InterfaceMethod(c, data);
        return method.IsSuccess ? Outcome<MethodInformationResult>.Success(new(method.Value, data.Object, lookup)) : method.Propagate<MethodInformationResult>();
    }

    private Outcome<MethodRef> InterfaceMethod(QueryContext c, InterfaceDataName data)
    {
        var named = c.Get(names, data.Interface);
        if (!named.IsSuccess || named.Value.Name is not EntityName { Entity: ClassEntity { Type: DefinitionRef type } }
            || !type.Definition.IsInterface || Open(type))
            return Outcome<MethodRef>.Failure(new("dispatch.interface-name", "接口没有具体的元数据类型名字。", named.Why));
        var methods = type.Definition.Methods.Where(m => m.Slot == data.Slot && !m.IsStatic).ToArray();
        if (methods.Length != 1) return Outcome<MethodRef>.Failure(new("dispatch.interface-slot-method", "接口槽号没有唯一方法。"));
        if (methods[0].GenericParameters.Count != 0) return Outcome<MethodRef>.Failure(new("dispatch.interface-generic-method", "泛型接口方法不在查询范围内。"));
        return Outcome<MethodRef>.Success(new(methods[0], type.Arguments, []));
    }

    private static Outcome<MethodInformationResult> Missing(string code, string detail, Reason? cause = null) =>
        Outcome<MethodInformationResult>.Failure(new("dispatch.method-" + code, detail, cause));
}
