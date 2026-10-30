using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>条件抛出折叠后，保留原落地点及沿入边携带的 SSA 值。</summary>
internal static class FoldedCheckEdges
{
    internal static bool Preserve(MachineFunction function, Block head, Block thrown, int edge, Func<Variable> fresh)
    {
        if (thrown.Handler is not { } handler || handler == head.Handler) return true;
        if (head.Handler is not null) return false;
        var incoming = MachineFunction.PredecessorIndex(head, edge);
        var outgoing = MachineFunction.PredecessorIndex(thrown, thrown.Successors.Count - 1);
        var aliases = thrown.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[incoming]);
        var constants = new List<Define>();
        foreach (var define in thrown.Statements.OfType<Define>())
        {
            if (define.Value is not Const || define.Target.Width != 64) return false;
            var variable = fresh();
            aliases[define.Target] = variable;
            constants.Add(define with { Target = variable });
        }
        var lifted = new Dictionary<Variable, Variable>();
        bool Reads(Stmt statement, Variable value) => statement is Phi phi ? phi.Sources.Contains(value)
            : ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == value);
        foreach (var variable in aliases.Keys)
        {
            if (!function.Blocks.Where(b => b != thrown).Any(b => b.Statements.Any(s => !(b == handler && s is Phi) && Reads(s, variable)))) continue;
            if (handler.Predecessors.ToArray() is not [var only] || only != thrown || variable.Width != 64) return false;
            lifted[variable] = fresh();
        }
        Variable Resolve(Variable variable)
        {
            var seen = new HashSet<Variable>();
            while (aliases.TryGetValue(variable, out var replacement) && seen.Add(variable)) variable = replacement;
            return variable;
        }
        var inputs = handler.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => Resolve(p.Sources[outgoing]));
        if (inputs.Values.Concat(lifted.Keys.Select(Resolve)).Any(aliases.ContainsKey)) return false;
        foreach (var block in function.Blocks.Where(b => b != thrown))
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is Phi phi)
                {
                    if (block != handler) block.Statements[i] = phi with { Sources = phi.Sources.Select(v => lifted.GetValueOrDefault(v, v)).ToArray() };
                }
                else block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e,
                    v => v is Use use && lifted.TryGetValue(use.Variable, out var replacement) ? new Use(replacement, use.Width) : null));
            }
        foreach (var (original, target) in lifted)
        {
            handler.Statements.Insert(0, new Phi(handler.Start, target, [original]));
            inputs[target] = Resolve(original);
        }
        head.Statements.InsertRange(head.Statements.Count - 1, constants);
        MachineFunction.AddEdge(head, handler);
        head.Handler = handler;
        for (var i = 0; i < handler.Statements.Count && handler.Statements[i] is Phi phi; i++)
            handler.Statements[i] = phi with { Sources = [.. phi.Sources, inputs[phi.Target]] };
        return true;
    }
}
