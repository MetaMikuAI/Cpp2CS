using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Ssa;

using Storage = Cpp2CS.Ir.Storage;

/// <summary>
/// SSA 修复：控制流复制后，给定变量有多个定义。把这些变量的定义与使用换成各自新的存储单元，再只对这些单元构建 SSA；
/// 其他 φ 以它们为来源时，在对应前驱末尾读出到达的版本。变量不能是 φ 的目标或调用的结果。
/// </summary>
public static class SsaRepair
{
    public static void Run(MachineFunction function, IReadOnlyCollection<Variable> variables, ICallModel calls, Storage stackPointer)
    {
        if (variables.Count == 0) return;
        var next = function.Blocks.SelectMany(b => b.Statements).SelectMany(Storages).Where(s => s.Bank == Bank.Temp)
            .Select(s => s.Index).DefaultIfEmpty(0).Max() + 1;
        var renamed = new Dictionary<Variable, Storage>();
        foreach (var variable in variables) renamed[variable] = new Storage(Bank.Temp, next++, variable.Width);
        Expr Map(Expr expression) => ExprMap.Map(expression, e => e is Use u && renamed.TryGetValue(u.Variable, out var s) ? new Read(s, u.Width) : null);
        var inserts = new List<(Block Block, Stmt Statement)>();
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                switch (statement)
                {
                    case Phi phi:
                        {
                            if (renamed.ContainsKey(phi.Target)) throw new InvalidOperationException($"SSA 修复不处理 φ 目标 {phi.Target}");
                            var sources = phi.Sources.ToArray();
                            for (var j = 0; j < sources.Length; j++)
                            {
                                if (sources[j] is not { } source || !renamed.TryGetValue(source, out var storage)) continue;
                                var temp = new Variable(new Storage(Bank.Temp, next++, source.Width), 1);
                                inserts.Add((block.Predecessors[j], new Define(phi.Address, temp, new Read(storage, source.Width))));
                                sources[j] = temp;
                            }
                            block.Statements[i] = phi with { Sources = sources };
                            break;
                        }
                    case Define define when renamed.TryGetValue(define.Target, out var target):
                        block.Statements[i] = new Assign(define.Address, target, Map(define.Value));
                        break;
                    case Call call when call.Defines.Any(d => d is not null && renamed.ContainsKey(d)):
                        throw new InvalidOperationException($"SSA 修复不处理调用结果 {call}");
                    default:
                        block.Statements[i] = ExprMap.MapOperands(statement, Map);
                        break;
                }
            }
        foreach (var (block, statement) in inserts)
        {
            var at = block.Statements.Count > 0 && block.Statements[^1] is Jump or Branch or IndirectJump or Return or Call { Kind: CallKind.Tail or CallKind.TailIndirect }
                ? block.Statements.Count - 1 : block.Statements.Count;
            block.Statements.Insert(at, statement);
        }
        var targets = renamed.Values.ToHashSet();
        SsaBuilder.Build(function, Dominators.Compute(function), targets.Contains, calls, stackPointer);
    }

    private static IEnumerable<Storage> Storages(Stmt statement)
    {
        foreach (var operand in ExprMap.Operands(statement))
            foreach (var e in ExprMap.Walk(operand))
                if (e is Use u) yield return u.Variable.Storage;
                else if (e is Read r) yield return r.Storage;
        switch (statement)
        {
            case Define d: yield return d.Target.Storage; break;
            case Phi p: yield return p.Target.Storage; break;
            case Assign a: yield return a.Target; break;
        }
    }
}
