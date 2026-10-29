using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>对象或字段地址合流后的读取及前置判空沿原入边展开，保留访问次序。</summary>
internal static class JoinedFieldReads
{
    internal static bool Run(MachineFunction function, Func<Phi, bool> differentReferences)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        var changed = false;
        var versions = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
        {
            Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines, _ => [],
        }).Where(v => v is not null).GroupBy(v => v.Storage).ToDictionary(g => g.Key, g => g.Max(v => v.Version) + 1);
        var label = Math.Max(1UL << 62, function.Blocks.Max(b => b.Start) + 1);
        foreach (var block in function.Blocks.ToArray())
        {
            if (block.IsLandingPad || block.Predecessors.Count is < 2 or > 4 || block.Predecessors.Distinct().Count() != block.Predecessors.Count
                || block.Predecessors.Any(p => p == block || p.Handler is not null || p.Successors.Count(s => s == block) != 1
                    || p.Successors.Count > 1 && p.Statements.LastOrDefault() is not Branch)) continue;
            var phis = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            var selected = phis.Values.Where(differentReferences).Select(p => p.Target).ToHashSet();
            if (selected.Count == 0 || phis.Values.Any(p => p.Sources.Length != block.Predecessors.Count)) continue;
            var prefix = new List<(Block Block, Stmt Statement)>();
            Define? read = null;
            var current = block;
            var seen = new HashSet<Block>();
            while (seen.Count < 3 && seen.Add(current))
            {
                foreach (var statement in current.Statements)
                {
                    if (statement is Nop or Jump || current == block && statement is Phi) continue;
                    if (statement is not Define && statement is not Call { Op.Kind: OpKind.NullCheck, Defines.Length: 0 }) break;
                    prefix.Add((current, statement));
                    if (prefix.Count > 16) break;
                    if (statement is not Define define) continue;
                    var expression = define.Value;
                    while (expression is Ir.Convert conversion) expression = conversion.Operand;
                    if (expression is Load { Width: 8 or 16 or 32 or 64 } load
                        && (load.Address is Use address && selected.Contains(address.Variable)
                            || load.Address is Binary { Op: BinOp.Add, Left: Use receiver, Right: Const { Value: > 0 } }
                                && selected.Contains(receiver.Variable))) { read = define; break; }
                }
                if (read is not null || prefix.Count > 16 || current.Statements.Any(s => s is not (Nop or Jump)
                    && !(current == block && s is Phi) && !prefix.Any(p => ReferenceEquals(p.Statement, s)))) break;
                if (current.NormalSuccessors.ToArray() is not [var next] || next.Predecessors.Count != 1 || next.Handler is not null) break;
                current = next;
            }
            if (read is null || prefix.Count > 16) continue;
            var moved = prefix.Select(p => p.Statement).OfType<Define>().Select(d => d.Target).ToArray();
            if (phis.Values.Any(p => p.Sources.Any(moved.Contains))) continue;
            var results = moved.ToDictionary(v => v, _ => new List<Variable>());
            for (var side = 0; side < block.Predecessors.Count; side++)
            {
                var parent = block.Predecessors[side];
                var renamed = moved.ToDictionary(v => v, v => v with { Version = versions[v.Storage]++ });
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use
                    ? phis.TryGetValue(use.Variable, out var phi) ? new Use(phi.Sources[side], use.Width)
                        : renamed.TryGetValue(use.Variable, out var fresh) ? new Use(fresh, use.Width) : null : null);
                var edge = new Block(label++) { End = label };
                foreach (var (_, original) in prefix)
                {
                    var mapped = ExprMap.MapOperands(original, OnEdge);
                    edge.Statements.Add(mapped is Define define ? define with { Target = renamed[define.Target] } : mapped);
                }
                edge.Statements.Add(new Jump(read.Address, block.Start));
                edge.Predecessors.Add(parent);
                edge.Successors.Add(block);
                parent.Successors[parent.Successors.IndexOf(block)] = edge;
                block.Predecessors[side] = edge;
                if (parent.Statements.LastOrDefault() is Branch branch)
                    parent.Statements[^1] = branch with { Target = branch.Target == block.Start ? edge.Start : branch.Target,
                        Fallthrough = branch.Fallthrough == block.Start ? edge.Start : branch.Fallthrough };
                else if (parent.Statements.LastOrDefault() is Jump jump) parent.Statements[^1] = jump with { Target = edge.Start };
                else parent.Statements.Add(new Jump(read.Address, edge.Start));
                function.Blocks.Add(edge);
                foreach (var variable in moved) results[variable].Add(renamed[variable]);
            }
            foreach (var (owner, statement) in prefix) owner.Statements.Remove(statement);
            block.Statements.InsertRange(0, moved.Select(v => new Phi(read.Address, v, results[v].ToArray())));
            changed = true;
        }
        if (changed) function.Renumber();
        return changed;
    }
}
