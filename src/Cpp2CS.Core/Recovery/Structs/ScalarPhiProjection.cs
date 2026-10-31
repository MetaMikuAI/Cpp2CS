using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

/// <summary>只观察低位的整数合流在入边建立窄快照，不要求来源寄存器的填充位有值。</summary>
internal static class ScalarPhiProjection
{
    internal static int Run(MachineFunction function)
    {
        if (function.Range.ExceptionRegions.Length != 0) return 0;
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, part =>
                    part is Use { Width: 8 or 16 or 32 } use ? CallArgumentProjection.Low(use, use.Width, definitions) : null));
        Cpp2CS.Machine.Ssa.Propagate.RemoveDead(function);
        var phis = function.Blocks.SelectMany(b => b.Statements.OfType<Phi>().Select(p => (Block: b, Phi: p)))
            .Where(p => p.Phi.Target.Width == 64).ToDictionary(p => p.Phi.Target);
        var links = phis.Values.SelectMany(p => p.Phi.Sources.Where(phis.ContainsKey)
            .SelectMany(s => new[] { (From: p.Phi.Target, To: s), (From: s, To: p.Phi.Target) }))
            .ToLookup(p => p.From, p => p.To);
        var observed = function.Blocks.SelectMany(b => b.Statements).SelectMany(ExprMap.Operands)
            .SelectMany(ExprMap.Walk).OfType<Use>().GroupBy(u => u.Variable)
            .ToDictionary(g => g.Key, g => g.Max(u => u.Width));
        var next = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
        {
            Define d => new[] { d.Target },
            Phi p => p.Sources.Prepend(p.Target),
            Call c => c.Defines,
            _ => Enumerable.Empty<Variable>(),
        }).Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        var seen = new HashSet<Variable>();
        var changed = 0;
        foreach (var target in phis.Keys)
        {
            if (seen.Contains(target)) continue;
            var web = new HashSet<Variable>();
            var pending = new Stack<Variable>();
            pending.Push(target);
            while (pending.TryPop(out var current))
                if (web.Add(current))
                    foreach (var linked in links[current]) pending.Push(linked);
            seen.UnionWith(web);
            var width = web.Max(v => observed.GetValueOrDefault(v));
            if (width is not (8 or 16 or 32) || web.Any(v => phis[v].Phi.Sources.Length != phis[v].Block.Predecessors.Count)
                || function.Blocks.SelectMany(b => b.Statements).OfType<Phi>().Any(p => !web.Contains(p.Target) && p.Sources.Any(web.Contains))) continue;
            // 已有窄定义和常量交由原类型推断，避免给枚举合流额外引入整数中间层。
            var roots = web.SelectMany(v => phis[v].Phi.Sources).Where(v => !web.Contains(v)).Distinct().ToArray();
            if (roots.All(v => definitions.GetValueOrDefault(v) is { } value && (value is Const || value.Width <= width
                || value is Ir.Convert { Kind: ConvKind.ZeroExtend } extend && extend.Operand.Width <= width))) continue;
            foreach (var variable in web)
            {
                var (block, phi) = phis[variable];
                var sources = phi.Sources.ToArray();
                for (var side = 0; side < sources.Length; side++)
                {
                    if (web.Contains(sources[side])) continue;
                    var predecessor = block.Predecessors[side];
                    var snapshot = new Variable(Storage.Temp(next++), 1);
                    var value = new Use(sources[side], width);
                    var position = predecessor.Statements.Count;
                    if (predecessor.Statements.LastOrDefault() is Jump or Branch or IndirectJump or Return) position--;
                    predecessor.Statements.Insert(position, new Define(phi.Address, snapshot, value));
                    sources[side] = snapshot;
                }
                block.Statements[block.Statements.IndexOf(phi)] = phi with { Sources = sources };
                changed++;
            }
        }
        return changed;
    }
}
