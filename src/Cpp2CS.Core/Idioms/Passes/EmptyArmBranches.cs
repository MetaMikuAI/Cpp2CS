using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

/// <summary>
/// 一臂只有 φ 与空语句、直接跳到另一臂的分支：条件不读内存时求值没有副作用，两条路到达汇合块时各 φ 取同一个值，分支等于直接跳到汇合块。
/// 尾合并后残留的、初始化已删除的守卫（只剩 beforefieldinit 的空语句）是这种形态。
/// </summary>
internal static class EmptyArmBranches
{
    public static bool Run(MachineFunction function)
    {
        var changed = false;
        foreach (var head in function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch branch || head.Handler is not null
                || ExprMap.Walk(branch.Condition).Any(e => e is Load)) continue;
            var normal = head.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0] == normal[1]) continue;
            for (var side = 0; side < 2; side++)
            {
                var (arm, join) = (normal[side], normal[1 - side]);
                if (arm.Handler is not null || arm.NormalSuccessors.ToArray() is not [var next] || next != join
                    || !arm.Statements.All(s => s is Phi or Nop or Jump)) continue;
                var (fromHead, armEdge, headEdge) = (arm.Predecessors.IndexOf(head), join.Predecessors.IndexOf(arm), join.Predecessors.IndexOf(head));
                if (fromHead < 0 || armEdge < 0 || headEdge < 0 || arm.Predecessors.Count(p => p == head) != 1
                    || join.Predecessors.Count(p => p == arm) != 1 || join.Predecessors.Count(p => p == head) != 1) continue;
                var passed = arm.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[fromHead]);
                bool Same(Phi phi) => (passed.TryGetValue(phi.Sources[armEdge], out var source) ? source : phi.Sources[armEdge]).Equals(phi.Sources[headEdge]);
                if (!join.Statements.OfType<Phi>().All(Same)) continue;
                head.Statements[^1] = new Jump(branch.Address, join.Start);
                MachineFunction.RemoveEdge(head, arm);
                changed = true;
                break;
            }
        }
        return changed;
    }
}
