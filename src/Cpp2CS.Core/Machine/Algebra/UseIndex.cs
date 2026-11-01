using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Algebra;

/// <summary>按语句顺序索引变量用途；重复读取保留次数。</summary>
internal sealed class UseIndex
{
    private readonly ILookup<Variable, Stmt> uses;
    public UseIndex(IEnumerable<Stmt> statements) => uses = statements.SelectMany(statement =>
        (statement is Phi phi ? phi.Sources : ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable))
        .Select(variable => (variable, statement))).ToLookup(p => p.variable, p => p.statement);
    public IEnumerable<Stmt> this[Variable variable] => uses[variable];
    public int Count(Variable variable) => uses[variable].Count();
}
