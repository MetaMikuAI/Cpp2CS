using Cpp2CS.Calls;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    internal readonly Dictionary<MethodRequest, NewObjectValue?> throwingConstructors = [];

    internal NewObjectValue? ThrowingConstructor(MethodRef callee, ulong address)
    {
        var request = new MethodRequest(callee, address);
        if (throwingConstructors.TryGetValue(request, out var known)) return known;
        NewObjectValue? result = null;
        if (callee.Method is { IsStatic: true, GenericParameters.Count: 0, Owner.GenericParameters.Count: 0 }
            && ManagedTypes.IsVoid(callee.Method.ReturnType) && callee.Method.Address == address
            && !callee.Method.Owner.Methods.Any(m => m.Name == ".cctor")
            && facts.Code.At(address) is { Region: CodeRegion.Managed, Size: <= 256 }
            && lifter.NoReturn.IsNoReturn(address)
            && new RecoveryScope(this, callee, address) { ExpandThrowCalls = false }.Run().Body is { } body
            && ThrowConstruction(body) is { } created && types.IsAssignable(created.Type, types.Corlib("System.Exception")))
            result = created;
        return throwingConstructors[request] = result;
    }

    /// <summary>只认单次异常构造后抛出的包装；参数按原顺序恰好使用一次，不省略或复制求值。</summary>
    internal static NewObjectValue? ThrowConstruction(ManagedBody body)
    {
        if (!body.Method.Method.IsStatic || !ManagedTypes.IsVoid(body.Method.Method.ReturnType)
            || body.Regions.Count != 0 || body.Blocks is not [var block]) return null;
        var created = block.Statements switch
        {
            [ManagedThrow { Exception: NewObjectValue value }] => value,
            [ManagedAssignment { Target: var local, Value: NewObjectValue value }, ManagedThrow { Exception: var thrown }]
                when local.Equals(thrown) => value,
            _ => null,
        };
        return created is { Transparent: false } && created.Arguments.All(v => v is ArgumentValue or ConstantValue or StringValue)
            && created.Arguments.OfType<ArgumentValue>().Select(a => a.Index).SequenceEqual(Enumerable.Range(0, body.Method.Method.Parameters.Count))
            ? created : null;
    }
}
