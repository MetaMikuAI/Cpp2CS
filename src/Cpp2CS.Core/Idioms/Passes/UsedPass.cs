using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class UsedPass
{
    internal static bool Used(this IdiomState state, Variable variable)
    {
        var seen = new HashSet<Variable>
        {
            variable
        };
        var work = new Stack<Variable>(seen);
        while (work.Count > 0)
        {
            var v = work.Pop();
            foreach (var stmt in state.function.Blocks.Where(b => !state.removed.Contains(b)).SelectMany(b => b.Statements))
            {
                if (stmt is Phi phi)
                {
                    if (phi.Sources.Contains(v) && seen.Add(phi.Target))
                        work.Push(phi.Target);
                    continue;
                }

                if (!ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == v))
                    continue;
                if (stmt is not Call call)
                    return true;
                if (call.Kind is CallKind.Direct or CallKind.Tail && call.Target is Const t && state.owner.calls.Signature(t.Value) is { } signature)
                {
                    // 非泛型调用的隐藏 MethodInfo 不参与托管参数语义；泛型调用仍保留实例身份依赖。
                    var methods = state.facts.EntriesAt(t.Value).Select(e => e.Method).OfType<MethodRef>().ToArray();
                    var hidden = methods.Length > 0 && methods.All(m => m.Method.GenericParameters.Count == 0 && m.Method.Owner.GenericParameters.Count == 0) ? signature.MethodInfo : null;
                    // 只有原生被调方确实读取的参数才保留合并值；未用寄存器可能只是元数据初始化的残值。
                    if (call.Arguments.Where((argument, i) => ExprMap.Walk(argument).OfType<Use>().Any(u => u.Variable == v) && (i >= call.Sources.Length || call.Sources[i] != hidden && !state.owner.UnusedInput(t.Value, call.Sources[i]))).Any())
                        return true;
                }

                if (ExprMap.Walk(call.Target).OfType<Use>().Any(u => u.Variable == v))
                    return true;
            }
        }

        return false;
    }
}
