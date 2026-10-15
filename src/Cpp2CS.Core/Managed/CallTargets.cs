using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>用调用处的 MethodInfo 选择共享实现的具体方法；替换前核对全部参数和返回存储。</summary>
public static class CallTargets
{
    public static MethodRef? Resolve(Call call, ManagedCallee callee, IManagedAbi abi, MetadataReferences metadata)
    {
        var candidates = new HashSet<MethodRef>();
        var hasMethodInfo = false;
        foreach (var owner in callee.Owners)
        {
            if (abi.Classify(owner.Method, out _) is not { MethodInfo: { } info } shape) continue;
            var index = Array.IndexOf(call.Sources, info.Register);
            if (index < 0 || index >= call.Arguments.Length || metadata.Usage(call.Arguments[index]) is not { } usage) continue;
            hasMethodInfo = true;
            if (usage.Value is not MethodRef target) continue;
            if (target.Method != owner.Method.Method || abi.Classify(target, out _) is not { } actual || !Compatible(shape, actual)) continue;
            candidates.Add(target);
        }
        if (hasMethodInfo) return candidates.Count == 1 ? candidates.Single() : null;
        // 引用类型泛型实现会用 object 作为共享代码的登记实例；唯一登记项不能证明调用处实参。
        if (callee.Owners is not [var single]) return null;
        return single.Method.TypeArguments.Concat(single.Method.MethodArguments).Any(ManagedTypes.IsReferenceType) ? null : single.Method;
    }

    private static bool Compatible(AbiSignature left, AbiSignature right) => left.MethodInfo == right.MethodInfo
        && Value(left.This, right.This) && Value(left.Return, right.Return)
        && left.Parameters.Length == right.Parameters.Length && left.Parameters.Zip(right.Parameters).All(p => Value(p.First, p.Second));

    private static bool Value(AbiValue? left, AbiValue? right)
    {
        if (left is null || right is null) return left is null && right is null;
        if (left.Passing != right.Passing || !left.Pieces.SequenceEqual(right.Pieces)) return false;
        return left.Type == right.Type || ManagedTypes.IsReferenceType(left.Type) && ManagedTypes.IsReferenceType(right.Type)
            || left.Type is ByRefRef a && right.Type is ByRefRef b && ManagedTypes.IsReferenceType(a.Element) && ManagedTypes.IsReferenceType(b.Element);
    }
}
