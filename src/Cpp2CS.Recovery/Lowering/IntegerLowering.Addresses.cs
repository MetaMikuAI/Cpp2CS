using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private ManagedValue? AddressArgument(Term term, TypeRef element)
    {
        // 已有托管指针形参只作同类型传递，不把它解释为另一个位置的地址。
        if (StaticType(term) is ByRefRef byref && byref.Element.Equals(element)) return Value(term);
        if (locations is null) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "取址实参缺少托管位置查询", code: "lowering.Address.Location");
        var address = context.Get(locations.Addresses, term);
        if (!address.IsSuccess) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "取址实参定位失败：" + address.Why, address.Why,
            address.Why?.Code == "address.frame" ? "lowering.Address.Frame" : "lowering.Address.Location");
        var exact = address.Value.Where(v => v.Type.Equals(element)).ToArray();
        if (exact.Length == 0) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "按引用实参的元素类型与地址末端声明类型不相同：" + element, code: "lowering.Address.Use");
        if (exact.Length != 1) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
            "取址实参有多个同类型的位置视图", code: "lowering.Address.Location");
        var view = exact[0];
        if (view.Path.Any(f => (f.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
            && !(method.Method.Name == ((f.Field.Attributes & System.Reflection.FieldAttributes.Static) != 0 ? ".cctor" : ".ctor") && method.Method.Owner == f.Field.Owner)))
            return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
                "取址实参可能改写构造函数上下文之外的只读字段", code: "lowering.Address.Use");
        if (view.Index is { } index)
        {
            var value = Value(index);
            if (value is null) return null;
            if (!IntegerType(value.Type)) return Fail<ManagedValue>(LoweringFailureKind.UnsupportedType,
                "数组元素取址的下标不是整数", code: "lowering.Address.Location");
        }
        var target = AccessView(view, write: true, address: true);
        return target is null ? null : new AddressValue(target, types.PointerSize * 8);
    }

    private bool RejectIndirectParameterUse(IEnumerable<Term> roots, string use)
    {
        if (!hasIndirectParameters) return false;
        foreach (var root in roots)
        {
            var resolved = context.Get(state.Resolve, root);
            if (!resolved.IsSuccess) continue;
            foreach (var term in SnapshotRewrite.Dependencies([resolved.Value]))
                if (indirectParameters.ContainsKey(term)
                    || valueNames is not null && context.Get(valueNames, term) is { IsSuccess: true, Value.Name: IndirectParameterName })
                {
                    Fail<object>(LoweringFailureKind.UnsupportedType, "间接形参的存储地址用于" + use, code: "lowering.IndirectParameter.Escape");
                    return true;
                }
        }
        return false;
    }

    private bool RejectAddressUse(IEnumerable<Term> roots, string use, bool frameContents = false)
    {
        var inputs = roots.ToArray();
        if (!frameContents && RejectIndirectParameterUse(inputs, use)) return true;
        if (locations is null) return false;
        foreach (var root in frameContents ? [] : inputs)
        {
            var frame = context.Get(frameAddressUses, root);
            if (frame.IsSuccess && !frame.Value.IsEmpty)
            {
                Fail<object>(LoweringFailureKind.UnsupportedType, "帧地址用于" + use, code: "lowering.Frame.Use");
                return true;
            }
        }
        foreach (var term in SnapshotRewrite.Dependencies(inputs))
            if (context.Get(locations.Addresses, term).IsSuccess && StaticType(term) is not ByRefRef)
            {
                Fail<object>(LoweringFailureKind.UnsupportedType, "托管地址用于" + use, code: "lowering.Address.Use");
                return true;
            }
        return false;
    }
}
