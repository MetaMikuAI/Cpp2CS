using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // null 绕过检查、非 null 经 sealed klass 检查后汇合；保留原抛出点，只为汇合后的同一 SSA 引用补类型。
        private bool CheckedNullableReference(Use value, TypeRef target, ulong address)
        {
            var uses = blocks.Where(b => b.Statements.Any(s => s.Address == address)).ToArray();
            if (uses is not [var use] || use.Predecessors.Count != 2) return false;
            foreach (var check in use.Predecessors)
            {
                if (check.Statements.LastOrDefault() is not Jump jump || jump.Target != use.Start
                    || check.Predecessors is not [var branchBlock] || !use.Predecessors.Contains(branchBlock)
                    || branchBlock.Statements.LastOrDefault() is not Branch { Condition: Compare test } branch)
                    continue;
                var nullEdge = test switch
                {
                    { Left: var left, Right: Const { Value: 0 }, Cond: Cond.Eq } when left == value => branch.Target,
                    { Left: var left, Right: Const { Value: 0 }, Cond: Cond.Ne } when left == value => branch.Fallthrough,
                    { Right: var right, Left: Const { Value: 0 }, Cond: Cond.Eq } when right == value => branch.Target,
                    { Right: var right, Left: Const { Value: 0 }, Cond: Cond.Ne } when right == value => branch.Fallthrough,
                    _ => 0UL,
                };
                if (nullEdge != use.Start || branch.Target != check.Start && branch.Fallthrough != check.Start) continue;
                if (check.Statements.OfType<Call>().Any(c => c is
                    { Op.Kind: OpKind.ThrowIf, Op.Operand: "System.InvalidCastException", Arguments: [Compare { Cond: Cond.Ne } comparison] }
                    && SealedOperands(comparison) is var (klass, checkedType) && checkedType.Equals(target)
                    && objectClasses.TryGetValue(klass, out var checkedValue) && checkedValue == value))
                    return true;
            }
            return false;
        }
    }
}
