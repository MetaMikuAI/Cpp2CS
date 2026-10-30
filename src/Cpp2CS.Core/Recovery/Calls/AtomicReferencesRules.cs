using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class AtomicReferencesRules
{
    internal static RecoveryFailure? CompareExchangeReference(this RecoveryScope ctx, Call call, List<ManagedStatement> output)
    {
        if (call.Arguments is not [var address, var value, var comparand] || call.Defines.FirstOrDefault() is not { } result)
            return RecoveryDiagnostics.Fail(call.Address, "原子交换 缺少位置、引用参数或返回值", rule: "CompareExchangeReference");
        if (!ctx.Location(address, 64).TryGet(out var location, out var failure))
            return failure;
        if (ctx.types.Kind(location.Type) != TypeKind.Reference)
            return RecoveryDiagnostics.Fail(call.Address, "原子交换 位置不是托管引用", rule: "CompareExchangeReference");
        var definition = ctx.types.CorlibDefinition("System.Threading.Interlocked")?.Methods.FirstOrDefault(m => m.Name == "CompareExchange" && m.IsStatic && m.GenericParameters.Count == 1 && m.Parameters.Count == 3 && m.Parameters[0].Type is ByRefRef { Element: GenericParameterRef { IsMethod: true, Position: 0 } } && m.Parameters.Skip(1).All(p => p.Type is GenericParameterRef { IsMethod: true, Position: 0 }) && m.ReturnType is GenericParameterRef { IsMethod: true, Position: 0 });
        if (definition is null)
            return RecoveryDiagnostics.Fail(call.Address, "原子交换 核心库缺少 Interlocked.CompareExchange<T>", rule: "CompareExchangeReference");
        var target = new MethodRef(definition, [], [location.Type]);
        if (!ctx.RecoverAs(value, location.Type, call.Address).TryGet(out var replacement, out failure))
            return failure;
        if (!ctx.RecoverAs(comparand, location.Type, call.Address).TryGet(out var expected, out failure))
            return failure;
        if (!ctx.Local(result).TryGet(out var local, out failure))
            return failure;
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(target, null, [new AddressValue(location), replacement, expected], false), local, false));
        if (call.Kind == CallKind.Tail)
            output.Add(new ManagedReturn(call.Address, local));
        return null;
    }
}
