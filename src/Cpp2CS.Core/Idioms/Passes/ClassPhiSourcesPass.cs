using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>
/// 对象的类指针与类常量比较相等之后，编译器在这一侧按相等传播，把常量传给 φ。
/// 被比较相等支配的入边上两者是同一个值：换回读取的类指针，合流后的类判断仍是对同一对象的类型检查，类常量不再作为值出现。
/// 只改只用于比较的 φ：作为运行时操作的类实参（装箱、分配）时，类常量正是操作的类。
/// </summary>
internal static class ClassPhiSourcesPass
{
    internal static bool ClassPhiSources(this IdiomState state)
    {
        var dominators = Dominators.Compute(state.function);
        var equal = new List<(Variable Klass, Symbol Class, Block From, Block To)>();
        foreach (var block in state.function.Blocks)
            if (block.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne } test } branch
                && (test.Left is Symbol ? (test.Right, test.Left) : (test.Left, test.Right)) is (Use { Width: 64 } klass, Symbol { Kind: SymbolKind.Class } expected)
                && state.RawDefinition(klass) is Load { Width: 64, Address: Use }
                && block.NormalSuccessors.FirstOrDefault(b => b.Start == (test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough)) is { } target)
                equal.Add((klass.Variable, expected, block, target));
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var index = 0; index < block.Statements.Count && block.Statements[index] is Phi phi; index++)
            {
                if (!OnlyCompared(state.function, phi.Target)) continue;
                var sources = phi.Sources.ToArray();
                for (var i = 0; i < sources.Length; i++)
                {
                    if (sources[i] is not { Width: 64 } source || state.RawDefinition(new Use(source, 64)) is not Symbol { Kind: SymbolKind.Class } constant) continue;
                    var parent = block.Predecessors[i];
                    var known = equal.FirstOrDefault(e => e.Class.Equals(constant)
                        && (e.From == parent && e.To == block && block.Predecessors.Count(p => p == parent) == 1
                            || e.To.Predecessors.Count == 1 && dominators.Dominates(e.To.Index, parent.Index)));
                    if (known.Klass is null) continue;
                    sources[i] = known.Klass;
                    changed = true;
                }
                block.Statements[index] = phi with { Sources = sources };
            }
        return changed;
    }

    /// <summary>变量的每次使用都是比较的一侧（不作其他运算的操作数、调用实参或 φ 来源）。</summary>
    private static bool OnlyCompared(MachineFunction function, Variable variable)
    {
        var (uses, compared) = (0, 0);
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is Phi { Sources: var sources } && sources.Contains(variable)) return false;
            foreach (var node in ExprMap.Operands(statement).SelectMany(ExprMap.Walk))
            {
                if (node is Use use && use.Variable.Equals(variable)) uses++;
                if (node is Compare test) compared += new[] { test.Left, test.Right }.Count(e => e is Use use && use.Variable.Equals(variable));
            }
        }
        return uses == compared;
    }
}
