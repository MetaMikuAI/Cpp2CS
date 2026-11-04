using Cpp2CS.Ir;

namespace Cpp2CS.Machine.Flow;

/// <summary>
/// 把语句复制到另一条控制路径。这是复制路径的唯一入口：操作数按映射改写，定义得到新变量，调用得到独立身份。
/// 映射先给出块入口 φ 在这条路径上的来源，之后随复制的定义增长。
/// </summary>
internal sealed class PathCopy(Func<Variable, Variable> fresh, Dictionary<Variable, Variable>? initial = null)
{
    public Dictionary<Variable, Variable> Map { get; } = initial ?? [];

    public Expr Rewrite(Expr expression) => ExprMap.Map(expression,
        value => value is Use use && Map.TryGetValue(use.Variable, out var replacement) ? new Use(replacement, use.Width) : null);

    public Stmt Copy(Stmt statement)
    {
        var mapped = ExprMap.MapOperands(statement, Rewrite);
        switch (mapped)
        {
            case Define define:
                {
                    var variable = fresh(define.Target);
                    Map[define.Target] = variable;
                    return define with { Target = variable };
                }
            case Call call:
                {
                    var variables = call.Defines.Select(v => v is null ? null! : fresh(v)).ToArray();
                    for (var i = 0; i < variables.Length; i++)
                        if (call.Defines[i] is { } old) Map[old] = variables[i];
                    return call.Duplicate() with { Defines = variables };
                }
            default:
                // 操作数未变时改写器返回原对象；每条路径仍需独立的语句身份。
                return mapped with { };
        }
    }
}
