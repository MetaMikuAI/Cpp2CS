using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class ArrayElementChecksRules
{
    internal static RecoveryFailure? ArrayElementCheck(this RecoveryScope ctx, Call call, Variable created, List<ManagedStatement> output)
    {
        if (!ctx.Recover(call.Arguments[1], null).TryGet(out var array, out var failure))
            return failure;
        if (array.Type is not ArrayRef)
            return RecoveryDiagnostics.Fail(call.Address, "数组元素检查缺少数组类型", rule: "ArrayElementCheck");
        if (!ctx.RecoverAs(call.Arguments[0], ctx.types.Object, call.Address).TryGet(out var value, out failure))
            return failure;
        var getType = ctx.types.CorlibMethod("System.Object", "GetType");
        var elementType = ctx.types.CorlibMethod("System.Type", "GetElementType");
        var instanceOf = ctx.types.CorlibMethod("System.Type", "IsInstanceOfType", ctx.types.Object);
        if (getType is null || elementType is null || instanceOf is null)
            return RecoveryDiagnostics.Fail(call.Address, "数组元素检查缺少类型反射方法", rule: "ArrayElementCheck");
        var runtimeType = ctx.StructLocal(ctx.types.Corlib("System.Type"), 64);
        var element = ctx.StructLocal(ctx.types.Corlib("System.Type"), 64);
        var matches = ctx.StructLocal(ctx.types.Boolean, 1);
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(getType, array, [], false), runtimeType, false));
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(elementType, runtimeType, [], true), element, false));
        output.Add(new ManagedCall(call.Address, new ManagedInvocation(instanceOf, element, [value], true), matches, false));
        return ctx.Assign(call.Address, created, () => new ChoiceValue(matches, value, new ConstantValue(0, ctx.types.Object, 64), ctx.types.Object, 64), output);
    }
}
