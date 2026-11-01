using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;



/// <summary>删除已确定或两侧等价的条件边；调用方随后清理不可达块并重新传播 SSA。</summary>
public static class ControlFlow
{
    public static bool Simplify(MachineFunction function)
    {
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch branch
                || ExprMap.Walk(branch.Condition).Any(e => e is Load or Intrinsic)) continue;
            var normal = block.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0].Start != branch.Target || normal[1].Start != branch.Fallthrough) continue;
            void Keep(int side)
            {
                block.Statements[^1] = new Jump(branch.Address, normal[side].Start);
                MachineFunction.RemoveEdgeAt(block, 1 - side);
                changed = true;
            }
            if (Fold.Simplify(branch.Condition) is Const constant)
            {
                Keep(constant.Value != 0 ? 0 : 1);
                continue;
            }
            if (normal[0] == normal[1])
            {
                var join = normal[0];
                var first = MachineFunction.PredecessorIndex(block, 0);
                var second = MachineFunction.PredecessorIndex(block, 1);
                if (join.Statements.OfType<Phi>().All(p => p.Sources[first] == p.Sources[second])) Keep(0);
                continue;
            }
            if (normal.All(b => b.Handler is null && !b.IsLandingPad && b.Successors.Count == 1 && b.Statements.All(s => s is Jump or Nop))
                && normal[0].Successors[0] == normal[1].Successors[0])
            {
                var join = normal[0].Successors[0];
                var first = MachineFunction.PredecessorIndex(normal[0], 0);
                var second = MachineFunction.PredecessorIndex(normal[1], 0);
                if (join.Statements.OfType<Phi>().All(p => p.Sources[first] == p.Sources[second]))
                {
                    Keep(0);
                    continue;
                }
            }
            for (var side = 0; side < 2; side++)
            {
                var empty = normal[side];
                var join = normal[1 - side];
                if (empty.Predecessors.Count != 1 || empty.Successors.Count != 1 || empty.Successors[0] != join
                    || empty.Handler is not null || empty.IsLandingPad || !empty.Statements.All(s => s is Jump or Nop)) continue;
                var direct = MachineFunction.PredecessorIndex(block, 1 - side);
                var indirect = MachineFunction.PredecessorIndex(empty, 0);
                if (!join.Statements.OfType<Phi>().All(p => p.Sources[direct] == p.Sources[indirect])) continue;
                Keep(1 - side);
                break;
            }
        }
        return changed;
    }
}
