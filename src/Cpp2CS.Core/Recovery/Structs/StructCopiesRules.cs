using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class StructCopiesRules
{
    /// <summary>完整值类型的定长复制先保存源值，再写入目标，保留 memmove 的重叠语义。</summary>
    [CallRule(22)]
    internal static RecoveryResult<bool> CopyStructValue(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (call is not { Kind: CallKind.Direct, Op: { Kind: OpKind.Import, Operand: "memcpy" or "memmove" }, Arguments: [var destination, var source, Const { Value: > 0 and <= 4096 } count] })
            return false;
        var used = ctx.blocks.SelectMany(b => b.Statements).SelectMany(s => s is Phi phi ? phi.Sources : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)).ToHashSet();
        if (call.Defines.Any(used.Contains))
            return false;
        var width = (int)count.Value * 8;
        if (!ctx.Values.CopyRanges(source, width).TryGet(out var sources, out _)
            || !ctx.Values.CopyRanges(destination, width).TryGet(out var targets, out _))
            return false;
        var pairs = (from fromValue in sources.Select(r => ctx.Values.WholeStructAt(r, width)).OfType<ManagedValue>().Distinct()
                     from toValue in targets.Select(r => ctx.Values.WholeStructAt(r, width)).OfType<ManagedValue>().Distinct()
                     where fromValue.Type.Equals(toValue.Type)
                     select (From: fromValue, To: toValue)).ToArray();
        if (pairs is not [var pair]) return false;
        // 完整值的读取在 CIL 求值栈上形成快照，随后才写目标；无需引入额外构造前局部。
        output.Add(pair.To is LocalValue local
            ? new ManagedAssignment(call.Address, local, pair.From)
            : new ManagedStore(call.Address, pair.To, pair.From));
        return true;
    }
}
