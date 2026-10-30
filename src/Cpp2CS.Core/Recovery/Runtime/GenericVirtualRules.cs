using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class GenericVirtualRules
{
    internal static void MarkGenericVirtualLoads(this RecoveryScope ctx)
    {
        Expr Instance(Expr expression)
        {
            var seen = new HashSet<Variable>();
            expression = ctx.Expand(expression);
            while (expression is Use use && seen.Add(use.Variable) && ctx.results.TryGetValue(use.Variable, out var produced) && produced.Call is { Op.Kind: OpKind.IsInst, Arguments: [var source] })
                expression = ctx.Expand(source);
            return expression;
        }

        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (call.Op is not { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic } || call.Target is not Use pointer || !ctx.values.TryGetValue(pointer.Variable, out var pointerValue) || pointerValue is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use info, Right: Const pointerOffset } } || pointerOffset.Value != RuntimeLayout.MethodVirtualPointer || !ctx.results.TryGetValue(info.Variable, out var result) || result.Call is not { Op: { Kind: OpKind.ResolveGenericVirtual, Operand: MethodRef resolved }, Arguments: [Use entry, _] } resolver || !resolved.Equals(generic) || !ctx.values.TryGetValue(entry.Variable, out var entryValue) || entryValue is not Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Use klass, Right: Const slotOffset } } || slotOffset.Value != (ulong)RuntimeLayout.VtableMethodInfo(generic.Method.Slot) || !ctx.values.TryGetValue(klass.Variable, out var klassValue) || klassValue is not Load { Width: 64, Address: var receiver } || call.Arguments.Length == 0 || Instance(receiver) != Instance(call.Arguments[0]))
                continue;
            ctx.State.Runtime.genericResolvers.Add(resolver);
            ctx.State.Runtime.runtime.UnionWith([pointer.Variable, info.Variable, entry.Variable, klass.Variable]);
        }
    }
}
