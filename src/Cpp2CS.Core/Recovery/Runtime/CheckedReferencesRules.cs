using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Recovery;

internal static class CheckedReferencesRules
{
    internal static void NormalizeCheckedObjects(this RecoveryScope ctx)
    {
        if (!ctx.PrepareTypeChecks())
            return;
        var changes = CheckedObjectAliases.Read(ctx.function, c => ctx.State.Runtime.typeChecks.GetValueOrDefault(c));
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (!changes.TryGetValue(old, out var mapped))
                    continue;
                ctx.Rewriter.Replace(block, i, mapped);
                if (old is Call { Op.Kind: OpKind.TypeCheck } before && mapped is Call { Op.Kind: OpKind.IsInst } after)
                {
                    ctx.State.Runtime.typeChecks.Remove(before);
                    ctx.State.Runtime.typeChecks.Remove(after);
                }
            }

        if (changes.Count > 0)
        {
            ctx.RemoveDeadDefinitions();
            ctx.definitions = ctx.IndexDefinitions();
        }

        ctx.MarkRuntime();
        ctx.InferTypes();
    }

    internal static bool CheckedReference(this RecoveryScope ctx, Use value, TypeRef target, ulong address)
    {
        if (ctx.CheckedNullableReference(value, target, address))
            return true;
        var sites = ctx.blocks.Where(b => b.Statements.Any(s => s.Address == address)).ToArray();
        if (sites is not [var site])
            return false;
        var dominators = Dominators.Compute(ctx.function);
        foreach (var block in ctx.blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use flag, Right: Const { Value: 0 } } test } branch
                || !ctx.results.TryGetValue(flag.Variable, out var source)
                || source.Call.Op is not { Kind: OpKind.TypeCheck, Operand: TypeRef checkedType } || !checkedType.Equals(target)
                || !ctx.State.Runtime.typeChecks.TryGetValue(source.Call, out var original) || original != value)
                continue;
            var success = block.NormalSuccessors.FirstOrDefault(b => b.Start == (test.Cond == Cond.Ne ? branch.Target : branch.Fallthrough));
            if (success is { Predecessors.Count: 1 } && dominators.Dominates(success.Index, site.Index))
                return true;
        }
        foreach (var block in ctx.blocks.Where(b => dominators.Dominates(b.Index, site.Index)))
            foreach (var check in block.Statements.Take(block == site ? block.Statements.FindIndex(s => s.Address == address) : block.Statements.Count).OfType<Call>())
            {
                // isinst 的原生继承检查返回 0/1；判空已排除失败路径，后续同一引用保留该类型。
                if (check is { Op.Kind: OpKind.NullCheck, Arguments: [Use flag] } && ctx.results.TryGetValue(flag.Variable, out var source) && source.Call.Op is { Kind: OpKind.TypeCheck, Operand: TypeRef checkedTarget } && checkedTarget.Equals(target) && ctx.State.Runtime.typeChecks.TryGetValue(source.Call, out var checkedObject) && checkedObject == value)
                    return true;
                if (check is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: Use failedFlag, Right: Const { Value: 0 } }] } && ctx.results.TryGetValue(failedFlag.Variable, out var checkedSource) && checkedSource.Call.Op is { Kind: OpKind.TypeCheck, Operand: TypeRef checkedReference } && checkedReference.Equals(target) && ctx.State.Runtime.typeChecks.TryGetValue(checkedSource.Call, out var original) && original == value)
                    return true;
                if (check is { Op.Kind: OpKind.ThrowIf, Arguments: [Compare { Cond: Cond.Ne } comparison] } && RuntimeRules.SealedOperands(comparison) is var (klass, checkedType) && checkedType.Equals(target) && ctx.State.Runtime.objectClasses.TryGetValue(klass, out var checkedValue) && checkedValue == value)
                    return true;
            }

        return false;
    }

    internal static bool CheckedNullableReference(this RecoveryScope ctx, Use value, TypeRef target, ulong address)
    {
        var uses = ctx.blocks.Where(b => b.Statements.Any(s => s.Address == address)).ToArray();
        if (uses is not [var site])
            return false;
        var dominators = Dominators.Compute(ctx.function);
        foreach (var use in ctx.blocks.Where(b => b.Predecessors.Count == 2 && dominators.Dominates(b.Index, site.Index)))
            foreach (var check in use.Predecessors)
            {
                if (check.Statements.LastOrDefault() is not Jump jump || jump.Target != use.Start)
                    continue;
                var path = new List<Cpp2CS.Machine.Flow.Block>
                {
                    check
                };
                var first = check;
                while (first.Predecessors is [var parent] && parent.Statements.LastOrDefault() is Jump to && to.Target == first.Start && !path.Contains(parent))
                {
                    path.Add(parent);
                    first = parent;
                }

                if (first.Predecessors is not [var branchBlock] || !use.Predecessors.Contains(branchBlock) || branchBlock.Statements.LastOrDefault() is not Branch { Condition: Compare test } branch)
                    continue;
                var nullEdge = test switch
                {
                    { Left: var left, Right: Const { Value: 0 }, Cond: Cond.Eq } when left == value => branch.Target,
                    { Left: var left, Right: Const { Value: 0 }, Cond: Cond.Ne } when left == value => branch.Fallthrough,
                    { Right: var right, Left: Const { Value: 0 }, Cond: Cond.Eq } when right == value => branch.Target,
                    { Right: var right, Left: Const { Value: 0 }, Cond: Cond.Ne } when right == value => branch.Fallthrough,
                    _ => 0UL,
                };
                if (nullEdge != use.Start || branch.Target != first.Start && branch.Fallthrough != first.Start)
                    continue;
                var calls = path.SelectMany(b => b.Statements).OfType<Call>().ToArray();
                if (calls.Any(c => c is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne } comparison] } && RuntimeRules.SealedOperands(comparison) is var (klass, checkedType) && checkedType.Equals(target) && ctx.State.Runtime.objectClasses.TryGetValue(klass, out var checkedValue) && checkedValue == value))
                    return true;
                foreach (var typed in calls.Where(c => c.Op?.Kind == OpKind.TypeCheck && Equals(c.Op.Operand, target) && ctx.State.Runtime.typeChecks.TryGetValue(c, out var checkedValue) && checkedValue == value))
                    if (typed.Defines.FirstOrDefault() is { } result && calls.Any(c => c is { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Eq, Left: Use flag, Right: Const { Value: 0 } }] } && flag.Variable == result))
                        return true;
            }

        return false;
    }
}
