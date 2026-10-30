using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class CollapsePass
{
    /// <summary>
    /// 把 head 的终结语句换成 insert + 跳到 merge，删去 head 的其他正常出边（区域由 Cleanup 删除）。
    /// merge 中各 φ 对新边的操作数取 via→merge 边上的操作数（via 为 head 时取原有的 head→merge 边），overrides 优先。
    /// </summary>
    internal static void Collapse(Block head, Block merge, Block via, List<Stmt> insert, Dictionary<Variable, Variable>? overrides, ulong address)
    {
        var viaIndex = merge.Predecessors.IndexOf(via);
        if (viaIndex < 0)
            throw new InvalidOperationException($"{via} 不是 {merge} 的前驱");
        var count = merge.Statements.TakeWhile(s => s is Phi).Count();
        var operands = new Variable[count];
        for (var i = 0; i < count; i++)
        {
            var phi = (Phi)merge.Statements[i];
            operands[i] = overrides is not null && overrides.TryGetValue(phi.Target, out var o) ? o : phi.Sources[viaIndex];
        }

        for (var k = head.NormalSuccessors.Count() - 1; k >= 0; k--)
            MachineFunction.RemoveEdgeAt(head, k);
        head.Statements.RemoveAt(head.Statements.Count - 1);
        head.Statements.AddRange(insert);
        head.Statements.Add(new Jump(address, merge.Start));
        MachineFunction.AddEdge(head, merge);
        for (var i = 0; i < count; i++)
        {
            var phi = (Phi)merge.Statements[i];
            merge.Statements[i] = phi with
            {
                Sources = [.. phi.Sources, operands[i]]
            };
        }
    }
}
