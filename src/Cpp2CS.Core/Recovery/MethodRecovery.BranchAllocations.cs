using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        // 分配后根据纯条件选择构造重载；每条路径恰好构造一次，同一个托管局部接收两臂的 newobj。
        private bool BranchConstructors(Block source, int index, Call allocation, DefinitionRef type, Variable created)
        {
            var middle = new List<Stmt>();
            foreach (var (block, statement) in AllocationPairing.Following(source, index))
            {
                if (statement is not Branch branch)
                {
                    if (AllocationPairing.Uses(statement, created)) return false;
                    middle.Add(statement);
                    continue;
                }
                if (AllocationPairing.Uses(branch, created) || ExprMap.Walk(branch.Condition).Any(e => e is Load or Intrinsic or Unknown)
                    || block.NormalSuccessors.ToArray() is not [var left, var right]) return false;
                var constructors = new List<Call>();
                foreach (var arm in new[] { left, right })
                {
                    if (arm.IsLandingPad || arm.Predecessors.Count != 1) return false;
                    var path = new List<Stmt>(middle);
                    foreach (var (current, candidate) in AllocationPairing.Following(arm, -1))
                    {
                        if (!AllocationPairing.Uses(candidate, created)) { path.Add(candidate); continue; }
                        if (candidate is not Call { Op: null } call || Receiver(call) is not Use receiver || receiver.Variable != created
                            || Resolve(call) is not { Method.Name: ".ctor", Method.IsStatic: false } constructor || constructor.Method.Owner != type.Definition
                            || AllocationPairing.MotionProblem(function.Range, source, allocation, current, call, path, created) is not null) return false;
                        constructors.Add(call);
                        break;
                    }
                }
                if (constructors.Count != 2) return false;
                dropped.Add(allocation);
                foreach (var constructor in constructors) constructed[constructor] = created;
                return true;
            }
            return false;
        }
    }
}
