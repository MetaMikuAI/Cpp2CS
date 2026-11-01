using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DirectPass
{
    internal static Call? Direct(this IdiomState state, Block block, int index, Call call)
    {
        if (state.owner.HelperOf(call) is not { } helper)
            return null;
        var args = call.Arguments;
        // 泛型虚方法：helper(vtable/接口槽的 method, m)，m 为封闭泛型方法；接口槽须匹配声明类型和槽号。
        if (args.Length >= 2 && state.defs.Expand(args[1]) is Symbol { Kind: SymbolKind.Method, Value: MethodRef generic } && generic.MethodArguments.Count > 0 && state.GenericVirtualSlot(state.defs.Expand(args[0]), generic) && call.Defines.FirstOrDefault() is { } resolved)
        {
            state.genericVirtual[resolved] = generic;
            state.Result.Hit(Template.GenericVirtualCall);
            return call with
            {
                Op = new RuntimeOp(OpKind.ResolveGenericVirtual, generic),
                Arguments = [args[0], args[1]],
                Sources = []
            };
        }

        if (helper.Kind == HelperKind.InitMetadata && args.Length > 0 && state.defs.Expand(args[0]) is Const slotAddress && state.facts.Usages.At(slotAddress.Value) is { } slot)
        {
            state.Result.InitializedSlots.Add(slotAddress.Value);
            state.Result.Hit(Template.LazyMetadataInit);
            state.lazyValues.Add((call, new Symbol(SymbolOfPass.SymbolOf(slot.Usage.Kind), slot.Usage.Value)));
            return null;
        }

        Expr Arg(int i) => i < args.Length ? args[i] : Expr.C(0, 64);
        (OpKind Kind, object? Operand, Expr[] Arguments)? op = helper.Kind switch
        {
            HelperKind.ObjectNew => (OpKind.NewObject, state.ClassOperand([Arg(0)]), [Arg(0)]),
            HelperKind.NewArray or HelperKind.NewArrayFull => (OpKind.NewArray, state.ClassOperand([Arg(0)]), [Arg(0), Arg(1)]),
            HelperKind.Box => (OpKind.Box, state.ClassOperand([Arg(0)]), [Arg(0), Arg(1)]),
            HelperKind.Unbox => (OpKind.Unbox, state.ClassOperand([Arg(0), Arg(1)]), [Arg(0), Arg(1)]),
            HelperKind.IsInst => (OpKind.IsInst, state.ClassOperand([Arg(0), Arg(1)]), [Arg(0), Arg(1)]),
            HelperKind.IsAssignableFrom => (OpKind.IsAssignableFrom, null, [Arg(0), Arg(1)]),
            HelperKind.ClassInit => (OpKind.RunClassConstructor, state.ClassOperand([Arg(0)]), [Arg(0)]),
            HelperKind.InitializedTypeInfo => (OpKind.InitClass, state.ClassOperand([Arg(0)]), [Arg(0)]),
            HelperKind.InitMethodRgctx => (OpKind.InitMethodRgctx, null, [Arg(0)]),
            HelperKind.Raise => (OpKind.Throw, null, [Arg(0)]),
            HelperKind.Throw => (OpKind.ThrowNew, helper.Detail, []),
            HelperKind.NullCheck => (OpKind.NullCheck, null, [Arg(0)]),
            HelperKind.GetException => (OpKind.NewException, helper.Detail, []),
            HelperKind.Rethrow => (OpKind.Rethrow, null, [Arg(0)]),
            HelperKind.MemoryBarrier => (OpKind.MemoryBarrier, null, []),
            HelperKind.CompareExchangeReference => (OpKind.CompareExchangeReference, null, [Arg(0), Arg(1), Arg(2)]),
            HelperKind.Terminate => (OpKind.Terminate, null, []),
            HelperKind.UnwindResume => (OpKind.ResumeUnwind, null, [Arg(0)]),
            HelperKind.FieldAddress => (OpKind.FieldAddress, null, [Arg(0), Arg(1)]),
            HelperKind.ArrayElementAddress => (OpKind.ArrayElementAddress, null, [Arg(0), Arg(1), Arg(2)]),
            HelperKind.Export => (OpKind.Export, helper.Detail, args),
            HelperKind.Import when helper.Detail == "__cxa_begin_catch" => (OpKind.BeginCatch, null, [Arg(0)]),
            HelperKind.Import when helper.Detail == "__cxa_end_catch" => (OpKind.EndCatch, null, []),
            HelperKind.Import => (OpKind.Import, helper.Detail, args),
            HelperKind.WriteBarrier when state.PrecedingStore(block, index, Arg(0), Arg(1)) => (OpKind.WriteBarrier, null, [Arg(0), Arg(1)]),
            _ => null,
        };
        if (op is not { } found)
            return null;
        state.Result.Hit(helper.Kind switch
        {
            HelperKind.WriteBarrier => Template.WriteBarrier,
            HelperKind.Import => Template.ImportCall,
            _ => Template.HelperCall,
        });
        return call with
        {
            Op = new RuntimeOp(found.Kind, found.Operand),
            Arguments = found.Arguments,
            Sources = []
        };
    }

    private static bool GenericVirtualSlot(this IdiomState state, Expr value, MethodRef method)
    {
        if (value is not Load { Width: 64 } load) return false;
        var (basis, offset) = SplitPass.Split(load.Address);
        if (basis is Load { Width: 64 } && offset == (ulong)RuntimeLayout.VtableMethodInfo(method.Method.Slot))
            return true;
        return offset == 8 && basis is Use data && state.interfaceData.TryGetValue(data.Variable, out var operand)
            && operand is ValueTuple<object?, int> slot && Equals(slot.Item1, method.DeclaringType) && slot.Item2 == method.Method.Slot;
    }
}
