using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Ssa;

/// <summary>传播条件边确定的完整位型：用于 φ 输入，以及没有其他前驱的目标块。</summary>
public static class EdgeConstants
{
    public static int Run(MachineFunction function)
    {
        var nextTemp = -1;
        Variable Fresh()
        {
            if (nextTemp < 0)
            {
                var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
                var variables = statements.SelectMany(s => s switch
                {
                    Define d => new[] { d.Target }, Phi p => p.Sources.Append(p.Target), Call c => c.Defines.Where(v => v is not null), _ => [],
                }).Concat(statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable));
                nextTemp = variables.Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
            }
            return new Variable(Storage.Temp(nextTemp++), 1);
        }

        var replaced = 0;
        foreach (var from in function.Blocks)
        {
            if (from.Statements.LastOrDefault() is not Branch branch || branch.Target == branch.Fallthrough) continue;
            var normal = from.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0].Start != branch.Target || normal[1].Start != branch.Fallthrough) continue;
            var constants = new Dictionary<Const, Variable>();
            for (var side = 0; side < 2; side++)
            {
                var facts = Facts(branch.Condition, side == 0);
                if (facts.Count == 0) continue;
                var target = normal[side];
                var incoming = target.Predecessors.IndexOf(from);
                if (incoming < 0) throw new InvalidOperationException("CFG 前驱与后继不一致");
                for (var i = 0; i < target.Statements.Count && target.Statements[i] is Phi phi; i++)
                {
                    var source = phi.Sources[incoming];
                    if (!facts.TryGetValue(source, out var constant) || constant.Width != phi.Target.Width) continue;
                    if (!constants.TryGetValue(constant, out var replacement))
                    {
                        constants.Add(constant, replacement = Fresh());
                        from.Statements.Insert(from.Statements.Count - 1, new Define(branch.Address, replacement, constant));
                    }
                    var sources = (Variable[])phi.Sources.Clone();
                    sources[incoming] = replacement;
                    target.Statements[i] = phi with { Sources = sources };
                    replaced++;
                }
                if (target.Predecessors.Count != 1) continue;
                for (var i = 0; i < target.Statements.Count; i++)
                {
                    var statement = target.Statements[i];
                    if (statement is Phi) continue;
                    var rewritten = ExprMap.MapOperands(statement, e =>
                    {
                        var mapped = ExprMap.Map(e, part => part is Use use && facts.TryGetValue(use.Variable, out var value) && use.Width <= value.Width
                            ? Fold.Convert(ConvKind.Truncate, value, use.Width) : null);
                        return ReferenceEquals(mapped, e) ? e : Fold.Simplify(mapped);
                    });
                    if (ReferenceEquals(statement, rewritten)) continue;
                    target.Statements[i] = rewritten;
                    replaced++;
                }
            }
        }
        return replaced;
    }

    private static Dictionary<Variable, Const> Facts(Expr condition, bool truth)
    {
        var result = new Dictionary<Variable, Const>();
        var conflicts = new HashSet<Variable>();
        void Add(Use use, Const constant)
        {
            // Temp 宽度为 64；部分寄存器比较不约束未比较的高位，浮点相等也不等于位型相同。
            if (use.Width != 64 || use.Variable.Width != 64 || constant.Width != 64 || conflicts.Contains(use.Variable)) return;
            if (result.TryGetValue(use.Variable, out var previous) && previous != constant)
            {
                result.Remove(use.Variable); conflicts.Add(use.Variable);
            }
            else result[use.Variable] = constant;
        }
        void Visit(Expr expression, bool value)
        {
            switch (expression)
            {
                case Not not: Visit(not.Operand, !value); break;
                case Logical logical when logical.IsAnd == value:
                    Visit(logical.Left, value); Visit(logical.Right, value); break;
                case Compare compare when compare.Cond == (value ? Cond.Eq : Cond.Ne):
                    if (compare is { Left: Use left, Right: Const right }) Add(left, right);
                    else if (compare is { Left: Const leftConstant, Right: Use rightUse }) Add(rightUse, leftConstant);
                    break;
            }
        }
        Visit(condition, truth);
        return result;
    }
}
