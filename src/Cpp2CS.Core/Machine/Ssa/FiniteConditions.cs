using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;



/// <summary>常量状态标志经 φ 汇合后，只沿单前驱路径收窄取值，消除异常清理生成的不可达出口。</summary>
internal sealed class FiniteConditions(MachineFunction function)
{
    public static bool Simplify(MachineFunction function)
    {
        FiniteConditions? finite = null;
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use, Right: Const } } branch) continue;
            var normal = block.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0].Start != branch.Target || normal[1].Start != branch.Fallthrough) continue;
            if ((finite ??= new FiniteConditions(function)).Side(block, branch) is not { } side) continue;
            block.Statements[^1] = new Jump(branch.Address, normal[side].Start);
            MachineFunction.RemoveEdgeAt(block, 1 - side);
            changed = true;
        }
        return changed;
    }

    private readonly Dictionary<Variable, Stmt> definitions = function.Blocks.SelectMany(b => b.Statements)
        .Where(s => s is Define or Phi).ToDictionary(s => s is Define d ? d.Target : ((Phi)s).Target);
    private readonly Dictionary<Variable, ulong[]?> values = [];

    private ulong[]? Values(Variable variable, HashSet<Variable> active)
    {
        if (values.TryGetValue(variable, out var cached)) return cached;
        if (!definitions.TryGetValue(variable, out var statement) || !active.Add(variable)) return null;
        ulong[]? result = null;
        if (statement is Define { Value: Const constant }) result = [constant.Value];
        else if (statement is Define { Value: Use use } && use.Width == variable.Width) result = Values(use.Variable, active);
        else if (statement is Phi phi)
        {
            var merged = new HashSet<ulong>();
            var valid = true;
            foreach (var source in phi.Sources.Distinct())
            {
                if (Values(source, active) is not { } incoming) { valid = false; break; }
                merged.UnionWith(incoming);
                if (merged.Count > 8) { valid = false; break; }
            }
            if (valid && merged.Count > 0) result = merged.ToArray();
        }
        active.Remove(variable);
        return values[variable] = result;
    }

    private int? Side(Block block, Branch branch)
    {
        if (branch.Condition is not Compare { Cond: Cond.Eq or Cond.Ne, Left: Use use, Right: Const constant }
            || use.Width != constant.Width || Values(use.Variable, []) is not { } possible) return null;
        var remaining = possible.Select(v => v & Expr.Mask(use.Width)).Distinct().ToHashSet();
        var child = block;
        var seen = new HashSet<Block> { child };
        // 单前驱说明每次进入 child 必定经过 parent 的该条边；SSA 值在沿途调用后仍不变。
        while (child.Predecessors.ToArray() is [var parent] && seen.Add(parent))
        {
            if (parent.Statements.LastOrDefault() is Branch previous
                && previous.Condition is Compare { Cond: Cond.Eq or Cond.Ne, Left: Use earlier, Right: Const compared } condition
                && earlier.Variable == use.Variable && earlier.Width == use.Width && compared.Width == use.Width
                && previous.Target != previous.Fallthrough && (child.Start == previous.Target || child.Start == previous.Fallthrough))
            {
                var truth = child.Start == previous.Target;
                remaining.RemoveWhere(v => (condition.Cond == Cond.Eq ? v == compared.Value : v != compared.Value) != truth);
            }
            child = parent;
        }
        var choices = remaining.Select(v => ((Compare)branch.Condition).Cond == Cond.Eq ? v == constant.Value : v != constant.Value).Distinct().ToArray();
        return choices is [var choice] ? choice ? 0 : 1 : null;
    }
}
