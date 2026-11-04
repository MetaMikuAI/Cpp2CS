using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>接口的不同槽位被尾合并时，按接收者来源拆回各自的查找和调用。</summary>
internal static class SharedInterfaceTails
{
    /// <summary>接口查找或虚表读取在同一间接调用前合流时，把调用放回对应的入边。</summary>
    internal static bool SplitInvokes(MachineFunction function, Func<Expr, Expr> expand)
    {
        var data = function.Blocks.SelectMany(b => b.Statements).OfType<Call>()
            .Where(c => c.Op?.Kind == OpKind.InterfaceInvokeData).SelectMany(c => c.Defines).ToHashSet();
        bool Pointer(Variable variable)
        {
            if (expand(new Use(variable, variable.Width)) is not Load { Width: 64 } load) return false;
            if (load.Address is Use address && data.Contains(address.Variable)) return true;
            var terms = TermsPass.Terms(load.Address).ToArray();
            var offset = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
            return terms.Where(e => e is not Const).ToArray() is [Load { Width: 64 }]
                && offset >= RuntimeLayout.ClassVtable && (offset - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0;
        }
        bool MergedClass(Block merge, Expr target)
        {
            if (expand(target) is not Load { Width: 64 } load) return false;
            var terms = TermsPass.Terms(load.Address);
            var offset = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
            return offset >= RuntimeLayout.ClassVtable && (offset - RuntimeLayout.ClassVtable) % RuntimeLayout.VirtualInvokeDataSize == 0
                && terms.Where(e => e is not Const).ToArray() is [Use klass]
                && merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == klass.Variable) is { } classes
                && classes.Sources.All(v => expand(new Use(v, 64)) is Load { Width: 64 });
        }
        return Cpp2CS.Machine.Ssa.TailDuplication.Run(function, merge =>
            merge.Statements.OfType<Call>().Any(call => call is { Op: null, Kind: CallKind.Indirect or CallKind.TailIndirect }
                && (call.Target is Use target && merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == target.Variable) is { } pointer
                    && pointer.Sources.All(Pointer) || MergedClass(merge, call.Target))));
    }

    internal static bool Run(MachineFunction function, Func<Call, bool> isLookup, Func<int, Variable> fresh)
    {
        var changed = false;
        var nextAddress = function.Blocks.Max(b => b.End) + 4;
        ulong Address() { var address = nextAddress; nextAddress += 4; return address; }
        foreach (var slow in function.Blocks.ToArray())
        {
            if (slow.Handler is not null || slow.IsLandingPad || slow.Predecessors.Count < 2
                || slow.Statements.OfType<Call>().ToArray() is not [var lookup] || !isLookup(lookup)
                || lookup.Arguments.Length < 3 || lookup.Arguments[0] is not Use receiver) continue;
            var bridges = new List<Block>();
            var slowExit = slow;
            while (slowExit.NormalSuccessors.ToArray() is [var bridge] && bridge != slow && !bridges.Contains(bridge)
                && bridge.Predecessors.Count == 1 && bridge.Handler is null && !bridge.IsLandingPad
                && bridge.Statements.All(s => s is Jump or Nop))
            {
                bridges.Add(bridge);
                slowExit = bridge;
            }
            if (slowExit.NormalSuccessors.ToArray() is not [var merge] || merge.Handler is not null || merge.IsLandingPad
                || merge.Predecessors.Count != 2
                || merge.Statements.OfType<Call>().ToArray() is not [Call { Op: null, Kind: CallKind.Indirect or CallKind.TailIndirect } invoke]) continue;
            var exits = merge.NormalSuccessors.ToArray();
            if (exits.Length > 1 || exits.Length == 0 && merge.Statements.LastOrDefault() is not (Return or Call { Kind: CallKind.TailIndirect })) continue;
            var exit = exits.SingleOrDefault();
            var hit = merge.Predecessors.Single(p => p != slowExit);
            if (hit.Handler is not null || hit.IsLandingPad || hit.Predecessors.Count is < 2 or > 16
                || hit.NormalSuccessors.ToArray() is not [var hitExit] || hitExit != merge
                || hit.Statements.Any(s => s is not (Phi or Define or Jump or Nop))) continue;
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            Expr Expanded(Variable variable)
            {
                Expr value = new Use(variable, variable.Width);
                var seen = new HashSet<Variable>();
                while (true)
                {
                    if (value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } converted) value = converted.Operand;
                    else if (value is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var definition)) value = definition;
                    else return value;
                }
            }
            ulong? Slot(Variable variable, bool fast) => Expanded(variable) switch
            {
                Const { Value: <= 32 } slot when !fast => slot.Value,
                Binary { Op: BinOp.Add, Width: 32, Right: Const { Value: <= 32 } slot } when fast => slot.Value,
                _ => null,
            };
            var partition = slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == receiver.Variable);
            var pair = partition is null ? null : merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources[merge.Predecessors.IndexOf(slowExit)] == partition.Target);
            var hitPartition = pair is null ? null : hit.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pair.Sources[merge.Predecessors.IndexOf(hit)]);
            var bySlot = hitPartition is null;
            if (bySlot)
            {
                // 同一接收者的不同接口槽也会共享尾部；以慢路径常量槽和快路径 offset + slot 对齐分支。
                if (lookup.Arguments[2] is not Use slotUse
                    || slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slotUse.Variable) is not { } slots
                    || slots.Sources.Any(v => Slot(v, false) is null)) continue;
                var candidates = hit.Statements.OfType<Phi>().Where(p => p.Sources.All(v => Slot(v, true) is { } n
                    && slots.Sources.Any(s => Slot(s, false) == n))).ToArray();
                if (candidates is not [var fastSlots]) continue;
                partition = slots;
                hitPartition = fastSlots;
            }
            var groups = partition!.Sources.Select((v, i) => (Value: v, Index: i)).GroupBy(p => p.Value).ToArray();
            if (groups.Length != hit.Predecessors.Count || groups.Any(g => slow.Statements.OfType<Phi>().Any(p => g.Select(x => p.Sources[x.Index]).Distinct().Count() != 1))) continue;
            var mapping = groups.Select(g => bySlot ? Array.FindIndex(hitPartition!.Sources, v => Slot(v, true) == Slot(g.Key, false))
                : Array.IndexOf(hitPartition!.Sources, g.Key)).ToArray();
            if (mapping.Any(i => i < 0) || mapping.Distinct().Count() != groups.Length) continue;
            var slotValid = lookup.Arguments[2] is Const { Value: <= 32 }
                || lookup.Arguments[2] is Use slot && slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slot.Variable) is { } slotPhi
                    && slotPhi.Sources.All(v => definitions.GetValueOrDefault(v) is Const { Value: <= 32 });
            if (!slotValid) continue;
            var split = new[] { slow, hit, merge };
            var shared = split.Concat(bridges).ToArray();
            if (split.Any(b => b.Statements.Any(s => s is not (Phi or Define or Call or Jump or Nop)
                    && !(b == merge && s is Return)))) continue;
            var defined = shared.SelectMany(b => b.Statements).SelectMany(Defines).ToHashSet();
            var exitIndex = exit?.Predecessors.IndexOf(merge) ?? -1;
            // 尾部结果只经原出口的对应 φ 入边流出，复制时按每条路径的变量映射续接。
            if (function.Blocks.Except(shared).Any(b => b.Statements.Any(s => s is Phi p
                ? p.Sources.Where((_, i) => b != exit || i != exitIndex).Any(defined.Contains)
                : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable))))) continue;
            var incoming = new[] { slow.Predecessors.ToArray(), hit.Predecessors.ToArray() };
            if (incoming.SelectMany(p => p).Any(p => p.Handler is not null || p.IsLandingPad || shared.Contains(p)
                || p.Successors.Distinct().Count() != p.Successors.Count
                || p.NormalSuccessors.Count() != 1 && p.Statements.LastOrDefault() is not Branch)) continue;
            var copies = new List<(Block Slow, Block Hit, Block Merge)>();
            var exitValues = exit?.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            for (var side = 0; side < groups.Length; side++)
            {
                var (slowCopy, slowMap) = Copy(slow, groups[side].First().Index, Address());
                var (hitCopy, hitMap) = Copy(hit, mapping[side], Address());
                var mergeAddress = Address();
                var mergeCopy = new Block(mergeAddress) { End = mergeAddress };
                var merged = new Dictionary<Variable, Variable>();
                foreach (var phi in merge.Statements.OfType<Phi>())
                {
                    var target = fresh(phi.Target.Width);
                    merged[phi.Target] = target;
                    var slowValue = phi.Sources[merge.Predecessors.IndexOf(slowExit)];
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
                    {
                        var value = exitValues![phi.Target];
                        exit.Statements[i] = phi with { Sources = [.. phi.Sources, merged.GetValueOrDefault(value, value)] };
                    }
                }
                copies.Add((slowCopy, hitCopy, mergeCopy));
            }
            for (var side = 0; side < groups.Length; side++)
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
                var copy = new Block(address) { End = address };
                Append(source, copy, map);
                return (copy, map);
            }
            void Append(Block source, Block copy, Dictionary<Variable, Variable> map)
            {
                var path = new PathCopy(v => fresh(v.Width), map);
                foreach (var statement in source.Statements.Where(s => s is not Phi))
                    copy.Statements.Add(path.Copy(statement));
            }
        }
        return changed;
    }

    private static IEnumerable<Variable> Defines(Stmt statement) => statement switch
    {
        Phi p => [p.Target],
        Define d => [d.Target],
        Call c => c.Defines.OfType<Variable>(),
        _ => [],
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
