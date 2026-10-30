using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class CallTrimmingRules
{
    internal static void TrimIndirectArguments(this RecoveryScope ctx, bool typed = false)
    {
        var changed = false;
        foreach (var block in ctx.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call)
                    continue;
                // 托管写入自带 GC 屏障；通知调用的地址实参不应保活原生地址计算及其 φ。
                if (ctx.IsWriteBarrier(call) && call.Arguments.Length > 0)
                {
                    ctx.Rewriter.Replace(block, i, Trimmed(call, [], []));
                    changed = true;
                    continue;
                }

                if ((typed ? ctx.Resolve(call) : ctx.Callee(call)) is not { } callee || ctx.owner.abi.Classify(callee, out _) is not { } signature)
                    continue;
                var reads = signature.Reads.ToHashSet();
                var keep = Enumerable.Range(0, call.Sources.Length).Where(k => reads.Contains(call.Sources[k])).ToArray();
                if (keep.Length != reads.Count)
                    continue;
                var widths = typed ? ctx.ScalarWidths(call, false, typed: true) : [];
                var args = keep.Select(k => widths.TryGetValue(call.Sources[k], out var width) && width > 0 ? ScalarVectorNarrowing.Low(call.Arguments[k], width) : call.Arguments[k]).ToArray();
                if (typed && signature.This is { Pieces: [var selfPiece] } self && ctx.UnusedInput(call, callee, self) && ctx.State.Signature.arguments.FirstOrDefault(p => p.Value.Index == -1 && ctx.types.IsAssignable(p.Value.Type, self.Type)) is { Value: not null } current)
                {
                    var position = Array.FindIndex(keep, k => call.Sources[k] == selfPiece.Register);
                    if (position >= 0 && ctx.DiscardableReceiver(args[position], []))
                        args[position] = new Use(new Variable(current.Key, 0), selfPiece.Width);
                }

                // 非泛型调用已绑定后，以方法身份承载隐藏参数，避免保活调用破坏的寄存器及循环 phi。
                if (typed && callee.Method.GenericParameters.Count == 0 && callee.Method.Owner.GenericParameters.Count == 0 && signature.MethodInfo is { } info)
                {
                    var position = Array.FindIndex(keep, k => call.Sources[k] == info.Register);
                    if (position >= 0)
                        args[position] = new Symbol(SymbolKind.Method, callee);
                }

                if (keep.Length == call.Sources.Length && args.AsSpan().SequenceEqual(call.Arguments))
                    continue;
                ctx.Rewriter.Replace(block, i, Trimmed(call, args, keep.Select(k => call.Sources[k]).ToArray()));
                changed = true;
            }

        if (!changed)
            return;
        ctx.RemoveDeadDefinitions();
        if (typed)
            ctx.definitions = ctx.IndexDefinitions();
        Call Trimmed(Call call, Expr[] arguments, Storage[] sources)
        {
            var replacement = call with
            {
                Arguments = arguments,
                Sources = sources
            };
            if (!typed)
                return replacement;
            ctx.Rewriter.Preserve(call, replacement);
            return replacement;
        }
    }

    internal static bool DiscardableReceiver(this RecoveryScope ctx, Expr value, HashSet<Variable> visited)
    {
        if (value is Use use)
        {
            if (!visited.Add(use.Variable) || use.Variable.Version <= 0 || ctx.results.ContainsKey(use.Variable))
                return true;
            if (ctx.values.TryGetValue(use.Variable, out var source))
                return ctx.DiscardableReceiver(source, visited);
            return ctx.blocks.SelectMany(b => b.Statements).OfType<Phi>().FirstOrDefault(p => p.Target == use.Variable) is { } phi && phi.Sources.All(v => ctx.DiscardableReceiver(new Use(v, use.Width), visited));
        }

        return value is Const or Unknown || value is Select select && ExprMap.Children(select).All(e => ctx.DiscardableReceiver(e, visited));
    }

    internal static bool IsWriteBarrier(this RecoveryScope ctx, Call call) => call.Op?.Kind == OpKind.WriteBarrier || call.Op is null && call.Target is Const helper && ctx.facts.Helpers.At(helper.Value) is { Kind: HelperKind.WriteBarrier } && ctx.facts.Code.RegionOf(helper.Value) != CodeRegion.Managed;
    internal static MethodRef? Callee(this RecoveryScope ctx, Call call)
    {
        switch (call.Op)
        {
            case { Kind: OpKind.CallMethodPointer or OpKind.CallDelegate, Operand: MethodRef pointerMethod }:
                return pointerMethod;
            case { Kind: OpKind.CallGenericVirtual, Operand: MethodRef generic } when generic.Method.IsVirtual:
                return generic;
            case { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: DefinitionRef itf } pair }:
                return itf.Definition.Methods.FirstOrDefault(m => m.Slot == pair.Item2 && !m.IsStatic) is { } method ? new MethodRef(method, itf.Arguments, []) : null;
            case { Kind: OpKind.CallVirtual, Operand: int slot } when call.Arguments.FirstOrDefault() is Use { Variable: var self }:
                var receiver = self.Version == 0 && ctx.State.Signature.arguments.TryGetValue(self.Storage, out var argument) ? argument.Type : ctx.function.Blocks.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(c => c.Op?.Kind == OpKind.NewObject && c.Defines.FirstOrDefault() == self)?.Op?.Operand as TypeRef;
                return receiver is DefinitionRef { Arguments.Count: 0, Definition: var type } && slot < type.VTable.Count && type.VTable[slot] is { Method.Owner.GenericParameters.Count: 0 } entry ? entry with
                {
                    TypeArguments = []
                }

                : null;
            default:
                return null;
        }
    }
}
