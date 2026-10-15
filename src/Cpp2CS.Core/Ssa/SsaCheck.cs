using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Ssa;

/// <summary>SSA 不变量检查：每个变量恰好定义一次；定义支配全部使用（φ 的操作数按对应前驱的末尾计）。</summary>
public static class SsaCheck
{
    public static List<string> Verify(MachineFunction function, Dominators dominators)
    {
        var errors = new List<string>();
        var definedAt = new Dictionary<Variable, (int Block, int Position)>();
        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                IEnumerable<Variable> defs = block.Statements[i] switch
                {
                    Define d => [d.Target],
                    Phi p => [p.Target],
                    Call c => c.Defines.Where(v => v is not null),
                    _ => [],
                };
                foreach (var v in defs)
                    if (!definedAt.TryAdd(v, (block.Index, i))) errors.Add($"{v} 重复定义 @0x{block.Statements[i].Address:x}");
            }
        }

        bool Available(Variable v, int block, int position) =>
            v.Version <= 0 || definedAt.TryGetValue(v, out var at) && (at.Block == block ? at.Position < position : dominators.Dominates(at.Block, block));

        foreach (var block in function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var stmt = block.Statements[i];
                if (stmt is Phi phi)
                {
                    if (i > 0 && block.Statements[i - 1] is not Phi) errors.Add($"{phi.Target} 不在块首");
                    if (phi.Sources.Length != block.Predecessors.Count) errors.Add($"{phi.Target} 操作数个数与前驱不符");
                    for (var j = 0; j < phi.Sources.Length && j < block.Predecessors.Count; j++)
                    {
                        var source = phi.Sources[j];
                        if (source is null) { errors.Add($"{phi.Target} 第 {j} 个操作数缺失"); continue; }
                        var predecessor = block.Predecessors[j];
                        if (!Available(source, predecessor.Index, predecessor.Statements.Count + 1)) errors.Add($"{phi.Target} 的操作数 {source} 不支配前驱 {predecessor}");
                    }
                    continue;
                }
                foreach (var use in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Use>())
                    if (!Available(use.Variable, block.Index, i)) errors.Add($"{use.Variable} 在 0x{stmt.Address:x} 使用时未定义或不支配");
                foreach (var read in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Read>().Where(r => r.Storage.Bank is Bank.Gpr or Bank.Vec or Bank.Flags))
                    errors.Add($"0x{stmt.Address:x} 仍有寄存器读 {read}");
            }
        }
        return errors;
    }
}
