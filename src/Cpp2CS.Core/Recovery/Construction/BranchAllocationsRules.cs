using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Idioms;

namespace Cpp2CS.Recovery;

internal static class BranchAllocationsRules
{
    internal static bool BranchConstructors(this RecoveryScope ctx, Block source, int index, Call allocation, DefinitionRef type, Variable created)
    {
        var middle = new List<Stmt>();
        foreach (var (block, statement) in AllocationPairing.Following(source, index))
        {
            if (statement is not Branch branch)
            {
                if (AllocationPairing.Uses(statement, created))
                    return false;
                middle.Add(statement);
                continue;
            }

            if (AllocationPairing.Uses(branch, created) || ExprMap.Walk(branch.Condition).Any(e => e is Load or Intrinsic or Unknown) || block.NormalSuccessors.ToArray() is not [var left, var right])
                return false;
            var constructors = new List<Call>();
            foreach (var arm in new[]
            {
                left,
                right
            }

            )
            {
                if (arm.IsLandingPad || arm.Predecessors.Count != 1)
                    return false;
                var path = new List<Stmt>(middle);
                foreach (var (current, candidate) in AllocationPairing.Following(arm, -1))
                {
                    if (!AllocationPairing.Uses(candidate, created))
                    {
                        path.Add(candidate);
                        continue;
                    }

                    if (candidate is not Call { Op: null } call || ConstructionRules.Receiver(call) is not Use receiver || receiver.Variable != created || ctx.Resolve(call) is not { Method.Name: ".ctor", Method.IsStatic: false } constructor || constructor.Method.Owner != type.Definition || AllocationPairing.MotionProblem(ctx.function.Range, source, allocation, current, call, path, created) is not null)
                        return false;
                    constructors.Add(call);
                    break;
                }
            }

            if (constructors.Count != 2)
                return false;
            ctx.State.Lowering.dropped.Add(allocation);
            foreach (var constructor in constructors)
                ctx.State.Construction.constructed[constructor] = created;
            return true;
        }

        return false;
    }
}
