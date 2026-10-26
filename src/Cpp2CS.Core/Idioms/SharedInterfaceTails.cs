using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>接口的不同槽位被尾合并时，按接收者来源拆回各自的查找和调用。</summary>
internal static class SharedInterfaceTails
{
    internal static bool Run(MachineFunction function, Func<Call, bool> isLookup, Func<Variable> fresh)
    {
        var changed = false;
        foreach (var slow in function.Blocks.ToArray())
        {
            if (slow.Handler is not null || slow.IsLandingPad || slow.Predecessors.Count != 2
                || slow.Statements.OfType<Call>().ToArray() is not [var lookup] || !isLookup(lookup)
                || lookup.Arguments.Length < 3 || lookup.Arguments[0] is not Use receiver || lookup.Arguments[2] is not Use slot
                || slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == receiver.Variable) is not { } receiverPhi
                || slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slot.Variable) is not { } slotPhi
                || slow.NormalSuccessors.ToArray() is not [var merge] || merge.Handler is not null || merge.IsLandingPad
                || merge.Predecessors.Count != 2 || merge.NormalSuccessors.ToArray() is not [var exit]
                || merge.Statements.OfType<Call>().ToArray() is not [Call { Op: null, Kind: CallKind.Indirect } invoke]) continue;
            var hit = merge.Predecessors.Single(p => p != slow);
            if (hit.Handler is not null || hit.IsLandingPad || hit.Predecessors.Count != 2
                || hit.NormalSuccessors.ToArray() is not [var hitExit] || hitExit != merge
                || hit.Statements.Any(s => s is not (Phi or Define or Jump or Nop))) continue;
            var pair = merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources[merge.Predecessors.IndexOf(slow)] == receiverPhi.Target);
            if (pair is null || hit.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pair.Sources[merge.Predecessors.IndexOf(hit)]) is not { } hitReceiver) continue;
            var mapping = receiverPhi.Sources.Select(v => Array.IndexOf(hitReceiver.Sources, v)).ToArray();
            if (mapping.Any(i => i < 0) || mapping.Distinct().Count() != 2) continue;
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            if (!slotPhi.Sources.All(v => definitions.GetValueOrDefault(v) is Const { Value: <= 32 })) continue;
            var shared = new[] { slow, hit, merge };
            if (shared.Any(b => b.End < b.Start + 8 || b.Statements.Any(s => s is not (Phi or Define or Call or Jump or Nop)))
                || shared.Any(b => function.Blocks.Any(other => other != b && other.Start == b.Start + 4))) continue;
            var defined = shared.SelectMany(b => b.Statements).SelectMany(Defines).ToHashSet();
            // 此形态调用返回 void，合并尾部的临时寄存器不能流出；外部 φ 由原边的输入原样复制。
            if (function.Blocks.Except(shared).SelectMany(b => b.Statements).Any(s => s is Phi p && p.Sources.Any(defined.Contains)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable)))) continue;
            var incoming = new[] { slow.Predecessors.ToArray(), hit.Predecessors.ToArray() };
            if (incoming.SelectMany(p => p).Any(p => p.NormalSuccessors.Count() != 1 || shared.Contains(p))) continue;
            var copies = new List<(Block Slow, Block Hit, Block Merge)>();
            var exitIndex = exit.Predecessors.IndexOf(merge);
            var exitValues = exit.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            for (var side = 0; side < 2; side++)
            {
                var (slowCopy, slowMap) = Copy(slow, side, slow.Start + (ulong)side * 4);
                var (hitCopy, hitMap) = Copy(hit, mapping[side], hit.Start + (ulong)side * 4);
                var mergeCopy = new Block(merge.Start + (ulong)side * 4) { End = merge.End };
                var merged = new Dictionary<Variable, Variable>();
                foreach (var phi in merge.Statements.OfType<Phi>())
                {
                    var target = fresh();
                    merged[phi.Target] = target;
                    var slowValue = phi.Sources[merge.Predecessors.IndexOf(slow)];
                    var hitValue = phi.Sources[merge.Predecessors.IndexOf(hit)];
                    mergeCopy.Statements.Add(new Phi(phi.Address, target, [slowMap.GetValueOrDefault(slowValue, slowValue), hitMap.GetValueOrDefault(hitValue, hitValue)]));
                }
                Append(merge, mergeCopy, merged);
                slowCopy.Statements.RemoveAll(s => s is Jump);
                hitCopy.Statements.RemoveAll(s => s is Jump);
                slowCopy.Statements.Add(new Jump(lookup.Address, mergeCopy.Start));
                hitCopy.Statements.Add(new Jump(hit.Statements.Last().Address, mergeCopy.Start));
                MachineFunction.AddEdge(slowCopy, mergeCopy);
                MachineFunction.AddEdge(hitCopy, mergeCopy);
                MachineFunction.AddEdge(mergeCopy, exit);
                for (var i = 0; i < exit.Statements.Count && exit.Statements[i] is Phi phi; i++)
                    exit.Statements[i] = phi with { Sources = [.. phi.Sources, exitValues[phi.Target]] };
                copies.Add((slowCopy, hitCopy, mergeCopy));
            }
            for (var side = 0; side < 2; side++)
            {
                Redirect(incoming[0][side], slow, copies[side].Slow);
                Redirect(incoming[1][mapping[side]], hit, copies[side].Hit);
            }
            // 原块已不可达；Renumber 删除原出口及其 φ 输入。
            function.Blocks.AddRange(copies.SelectMany(c => new[] { c.Slow, c.Hit, c.Merge }));
            function.Renumber();
            changed = true;

            (Block, Dictionary<Variable, Variable>) Copy(Block source, int side, ulong address)
            {
                var map = source.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[side]);
                var copy = new Block(address) { End = source.End };
                Append(source, copy, map);
                return (copy, map);
            }
            void Append(Block source, Block copy, Dictionary<Variable, Variable> map)
            {
                foreach (var statement in source.Statements.Where(s => s is not Phi))
                {
                    var mapped = ExprMap.MapOperands(statement, e => ExprMap.Map(e,
                        value => value is Use u && map.TryGetValue(u.Variable, out var replacement) ? new Use(replacement, u.Width) : null));
                    if (mapped is Define d)
                    {
                        var variable = fresh(); map[d.Target] = variable;
                        mapped = d with { Target = variable };
                    }
                    else if (mapped is Call call)
                    {
                        var variables = call.Defines.Select(v => v is null ? null! : fresh()).ToArray();
                        for (var i = 0; i < variables.Length; i++) if (call.Defines[i] is { } old) map[old] = variables[i];
                        mapped = call with { Defines = variables };
                    }
                    copy.Statements.Add(mapped);
                }
            }
        }
        return changed;
    }

    private static IEnumerable<Variable> Defines(Stmt statement) => statement switch
    {
        Phi p => [p.Target], Define d => [d.Target], Call c => c.Defines.OfType<Variable>(), _ => [],
    };

    private static void Redirect(Block predecessor, Block old, Block replacement)
    {
        MachineFunction.RemoveEdge(predecessor, old);
        MachineFunction.AddEdge(predecessor, replacement);
        if (predecessor.Statements.LastOrDefault() is Jump jump) predecessor.Statements[^1] = jump with { Target = replacement.Start };
        else predecessor.Statements.Add(new Jump(predecessor.End, replacement.Start));
    }
}
