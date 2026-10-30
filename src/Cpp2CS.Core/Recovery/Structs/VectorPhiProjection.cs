using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>高半部确定为零的向量汇合按两个 32 位分量投影，保留原定义处的快照。</summary>
internal static class VectorPhiProjection
{
    internal static int Run(IReadOnlyList<Block> blocks)
    {
        var statements = blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target);
        var phis = statements.OfType<Phi>().ToArray();
        var targets = phis.Where(p => p.Target.Storage.Bank == Bank.Vec).ToDictionary(p => p.Target);
        var parent = new Dictionary<Variable, Variable>();
        Variable Find(Variable v)
        {
            while (parent[v] != v) v = parent[v] = parent[parent[v]];
            return v;
        }
        foreach (var phi in targets.Values)
        {
            parent.TryAdd(phi.Target, phi.Target);
            foreach (var source in phi.Sources)
            {
                parent.TryAdd(source, source);
                parent[Find(source)] = Find(phi.Target);
            }
        }
        var accepted = new HashSet<Variable>();
        foreach (var web in parent.Keys.GroupBy(Find))
        {
            var members = web.ToHashSet();
            var roots = members.Where(v => !targets.ContainsKey(v)).ToArray();
            if (roots.Length == 0 || roots.Any(v => v.Version <= 0 || !definitions.TryGetValue(v, out var d)
                || d.Value is not (Const { Width: 128 } or Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 128, Operand.Width: 64 }))) continue;
            // 不把分量投影冒充仍由其他 φ 观察的完整寄存器。
            if (phis.Any(p => !targets.ContainsKey(p.Target) && p.Sources.Any(members.Contains))) continue;
            accepted.UnionWith(members);
        }
        if (accepted.Count == 0) return 0;
        var next = statements.SelectMany(s => s switch
        {
            Define d => new[] { d.Target },
            Phi p => p.Sources.Prepend(p.Target),
            Call c => c.Defines,
            _ => Enumerable.Empty<Variable>(),
        }).Concat(statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable))
            .Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        var pieces = accepted.ToDictionary(v => v, _ => new[] { new Variable(Storage.Temp(next++), 1), new Variable(Storage.Temp(next++), 1) });
        foreach (var block in blocks)
        {
            var rewritten = new List<Stmt>();
            var joined = new List<Stmt>();
            foreach (var statement in block.Statements)
            {
                if (statement is Phi phi && targets.ContainsKey(phi.Target) && pieces.TryGetValue(phi.Target, out var lanes))
                {
                    for (var i = 0; i < 2; i++) rewritten.Add(new Phi(phi.Address, lanes[i], phi.Sources.Select(s => pieces[s][i]).ToArray()));
                    var packed = new Insert(new Insert(Expr.C(0, 64), new Use(lanes[0], 32), 0), new Use(lanes[1], 32), 32);
                    joined.Add(new Define(phi.Address, phi.Target, new Ir.Convert(ConvKind.ZeroExtend, packed, 128)));
                    continue;
                }
                if (statement is not Phi && joined.Count > 0)
                {
                    rewritten.AddRange(joined);
                    joined.Clear();
                }
                rewritten.Add(statement);
                if (statement is not Define define || !pieces.TryGetValue(define.Target, out var inputs)) continue;
                // 常量直接分片；其他值从原定义的寄存器快照取片，不重读内存、不复制运算。
                Expr snapshot = define.Value is Const constant ? constant : new Use(define.Target, 128);
                for (var i = 0; i < 2; i++) rewritten.Add(new Define(define.Address, inputs[i], Fold.Extract(snapshot, i * 32, 32)));
            }
            rewritten.AddRange(joined);
            block.Statements.Clear();
            block.Statements.AddRange(rewritten);
        }
        return accepted.Count(targets.ContainsKey);
    }
}
