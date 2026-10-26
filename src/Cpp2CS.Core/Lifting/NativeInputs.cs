using Cpp2CS.Ir;

namespace Cpp2CS.Lifting;

/// <summary>未化简 SSA 的入口读取；未知指令或不完整控制流不能证明参数未用。</summary>
internal static class NativeInputs
{
    public static HashSet<Storage>? Reads(LiftedFunction lifted, Func<Call, Storage, bool>? unused = null)
    {
        var statements = lifted.Function.Blocks.SelectMany(b => b.Statements).ToArray();
        if (!lifted.Succeeded || lifted.Function.Problems.Count != 0 || lifted.Function.UnresolvedIndirectJumps != 0
            || statements.Any(s => s is Opaque or IndirectJump { Targets.Length: 0 })) return null;
        if (unused is null)
            return statements.SelectMany(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
                    .Concat(s is Phi phi ? phi.Sources : []))
                .Where(v => v.Version == 0).Select(v => v.Storage).ToHashSet();
        var definitions = new Dictionary<Variable, Variable[]>();
        var roots = new HashSet<Variable>();
        Variable[] Uses(IEnumerable<Expr> expressions) => expressions.SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable).ToArray();
        foreach (var statement in statements)
        {
            if (statement is Phi phi) definitions[phi.Target] = phi.Sources;
            else if (statement is Define define) definitions[define.Target] = Uses([define.Value]);
        }
        bool CarriesEntry(Expr value)
        {
            var pending = new Stack<Variable>(Uses([value]));
            var seen = new HashSet<Variable>();
            while (pending.TryPop(out var variable))
            {
                if (variable.Version == 0) return true;
                if (seen.Add(variable) && definitions.TryGetValue(variable, out var inputs))
                    foreach (var input in inputs) pending.Push(input);
            }
            return false;
        }
        foreach (var statement in statements)
        {
            if (statement is Phi) continue;
            else if (statement is Define define)
            {
                var inputs = Uses([define.Value]);
                // 访存及未知运算仍是读取证据，不能因调用不消费结果而抹掉潜在异常。
                if (ExprMap.Walk(define.Value).Any(e => e is Load or Intrinsic)) roots.UnionWith(inputs);
            }
            else if (statement is Call call)
                roots.UnionWith(Uses([call.Target, .. call.Arguments.Where((value, i) => i >= call.Sources.Length
                    || !CarriesEntry(value) || !unused(call, call.Sources[i]))]));
            else roots.UnionWith(Uses(ExprMap.Operands(statement)));
        }
        var pending = new Stack<Variable>(roots);
        while (pending.TryPop(out var variable))
            if (definitions.TryGetValue(variable, out var inputs))
                foreach (var input in inputs) if (roots.Add(input)) pending.Push(input);
        return roots.Where(v => v.Version == 0).Select(v => v.Storage).ToHashSet();
    }
}
