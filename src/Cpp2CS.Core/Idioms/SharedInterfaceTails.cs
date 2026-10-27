using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>接口的不同槽位被尾合并时，按接收者来源拆回各自的查找和调用。</summary>
internal static class SharedInterfaceTails
{
    /// <summary>已识别的接口查找在同一间接调用前合流时，把调用放回对应的入边。</summary>
    internal static bool SplitInvokes(MachineFunction function, Func<Expr, Expr> expand, Func<Variable> fresh)
    {
        var changed = false;
        var data = function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c.Op?.Kind == OpKind.InterfaceInvokeData).SelectMany(c => c.Defines).ToHashSet();
        foreach (var merge in function.Blocks.ToArray())
        {
            if (!function.Blocks.Contains(merge) || merge.Handler is not null || merge.IsLandingPad
                || merge.Predecessors.Count < 2 || merge.NormalSuccessors.ToArray() is not [var exit]
                || merge.Statements.Any(s => s is not (Phi or Define or Call or Jump or Nop))
                || merge.Statements.OfType<Call>().ToArray() is not [Call { Op: null, Kind: CallKind.Indirect, Target: Use target }]
                || merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == target.Variable) is not { } pointer
                || !pointer.Sources.All(v => expand(new Use(v, v.Width)) is Load { Width: 64, Address: Use address } && data.Contains(address.Variable))) continue;
            var incoming = merge.Predecessors.ToArray();
            if (incoming.Distinct().Count() != incoming.Length || incoming.Any(p => p == merge || p == exit || p.Handler is not null || p.IsLandingPad
                || p.NormalSuccessors.ToArray() is not [var next] || next != merge || p.Statements.LastOrDefault() is Branch)) continue;
            var defined = merge.Statements.SelectMany(Defines).ToHashSet();
            // 尾部的定义只供该次调用使用；流出的返回值与外部 φ 需另行建模。
            if (function.Blocks.Where(b => b != merge).SelectMany(b => b.Statements).Any(s => s is Phi phi && phi.Sources.Any(defined.Contains)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable)))) continue;
            var exitIndex = exit.Predecessors.IndexOf(merge);
            var exitValues = exit.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            var statements = merge.Statements.ToArray();
            var phis = statements.OfType<Phi>().ToArray();
            for (var side = 0; side < incoming.Length; side++)
            {
                var predecessor = incoming[side];
                var map = phis.ToDictionary(p => p.Target, p => p.Sources[side]);
                predecessor.Statements.RemoveAll(s => s is Jump);
                foreach (var statement in statements.Where(s => s is not (Phi or Jump)))
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
                    predecessor.Statements.Add(mapped);
                }
                Redirect(predecessor, merge, exit);
                for (var i = 0; i < exit.Statements.Count && exit.Statements[i] is Phi phi; i++)
                    exit.Statements[i] = phi with { Sources = [.. phi.Sources, exitValues[phi.Target]] };
            }
            function.Renumber();
            changed = true;
        }
        return changed;
    }

    internal static bool Run(MachineFunction function, Func<Call, bool> isLookup, Func<Variable> fresh)
    {
        var changed = false;
        foreach (var slow in function.Blocks.ToArray())
        {
            if (slow.Handler is not null || slow.IsLandingPad || slow.Predecessors.Count < 2
                || slow.Statements.OfType<Call>().ToArray() is not [var lookup] || !isLookup(lookup)
                || lookup.Arguments.Length < 3 || lookup.Arguments[0] is not Use receiver
                || slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == receiver.Variable) is not { } receiverPhi
                || slow.NormalSuccessors.ToArray() is not [var merge] || merge.Handler is not null || merge.IsLandingPad
                || merge.Predecessors.Count != 2
                || merge.Statements.OfType<Call>().ToArray() is not [Call { Op: null, Kind: CallKind.Indirect } invoke]) continue;
            var exits = merge.NormalSuccessors.ToArray();
            if (exits.Length > 1 || exits.Length == 0 && merge.Statements.LastOrDefault() is not Return { Value: null }) continue;
            var exit = exits.SingleOrDefault();
            var hit = merge.Predecessors.Single(p => p != slow);
            if (hit.Handler is not null || hit.IsLandingPad || hit.Predecessors.Count != 2
                || hit.NormalSuccessors.ToArray() is not [var hitExit] || hitExit != merge
                || hit.Statements.Any(s => s is not (Phi or Define or Jump or Nop))) continue;
            var pair = merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources[merge.Predecessors.IndexOf(slow)] == receiverPhi.Target);
            if (pair is null || hit.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pair.Sources[merge.Predecessors.IndexOf(hit)]) is not { } hitReceiver) continue;
            var groups = receiverPhi.Sources.Select((v, i) => (Value: v, Index: i)).GroupBy(p => p.Value).ToArray();
            if (groups.Length != 2 || groups.Any(g => slow.Statements.OfType<Phi>().Any(p => g.Select(x => p.Sources[x.Index]).Distinct().Count() != 1))) continue;
            var mapping = groups.Select(g => Array.IndexOf(hitReceiver.Sources, g.Key)).ToArray();
            if (mapping.Any(i => i < 0) || mapping.Distinct().Count() != 2) continue;
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            var slotValid = lookup.Arguments[2] is Const { Value: <= 32 }
                || lookup.Arguments[2] is Use slot && slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slot.Variable) is { } slotPhi
                    && slotPhi.Sources.All(v => definitions.GetValueOrDefault(v) is Const { Value: <= 32 });
            if (!slotValid) continue;
            var shared = new[] { slow, hit, merge };
            if (shared.Any(b => b.End < b.Start + 8 || b.Statements.Any(s => s is not (Phi or Define or Call or Jump or Nop)
                    && !(b == merge && s is Return { Value: null })))
                || shared.Any(b => function.Blocks.Any(other => other != b && other.Start == b.Start + 4))) continue;
            var defined = shared.SelectMany(b => b.Statements).SelectMany(Defines).ToHashSet();
            // 此形态调用返回 void，合并尾部的临时寄存器不能流出；外部 φ 由原边的输入原样复制。
            if (function.Blocks.Except(shared).SelectMany(b => b.Statements).Any(s => s is Phi p && p.Sources.Any(defined.Contains)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable)))) continue;
            var incoming = new[] { slow.Predecessors.ToArray(), hit.Predecessors.ToArray() };
            if (incoming.SelectMany(p => p).Any(p => p.Handler is not null || p.IsLandingPad || shared.Contains(p)
                || p.Successors.Distinct().Count() != p.Successors.Count
                || p.NormalSuccessors.Count() != 1 && p.Statements.LastOrDefault() is not Branch)) continue;
            var copies = new List<(Block Slow, Block Hit, Block Merge)>();
            var exitIndex = exit?.Predecessors.IndexOf(merge) ?? -1;
            var exitValues = exit?.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            for (var side = 0; side < 2; side++)
            {
                var (slowCopy, slowMap) = Copy(slow, groups[side].First().Index, slow.Start + (ulong)side * 4);
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
                if (exit is not null)
                {
                    MachineFunction.AddEdge(mergeCopy, exit);
                    for (var i = 0; i < exit.Statements.Count && exit.Statements[i] is Phi phi; i++)
                        exit.Statements[i] = phi with { Sources = [.. phi.Sources, exitValues![phi.Target]] };
                }
                copies.Add((slowCopy, hitCopy, mergeCopy));
            }
            for (var side = 0; side < 2; side++)
            {
                foreach (var source in groups[side]) Redirect(incoming[0][source.Index], slow, copies[side].Slow);
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
        var edge = predecessor.Successors.IndexOf(old);
        MachineFunction.RemoveEdgeAt(predecessor, edge);
        predecessor.Successors.Insert(edge, replacement);
        replacement.Predecessors.Add(predecessor);
        if (predecessor.Statements.LastOrDefault() is Jump jump) predecessor.Statements[^1] = jump with { Target = replacement.Start };
        else if (predecessor.Statements.LastOrDefault() is Branch branch) predecessor.Statements[^1] = branch with
            { Target = branch.Target == old.Start ? replacement.Start : branch.Target, Fallthrough = branch.Fallthrough == old.Start ? replacement.Start : branch.Fallthrough };
        else predecessor.Statements.Add(new Jump(predecessor.End, replacement.Start));
    }
}
