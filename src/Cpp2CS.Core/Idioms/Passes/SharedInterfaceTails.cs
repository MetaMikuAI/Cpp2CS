using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

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
                || merge.Predecessors.Count(p => p == slowExit) != 1
                || merge.Statements.OfType<Call>().FirstOrDefault(c => c.Kind is CallKind.Indirect or CallKind.TailIndirect) is not { Op: null } invoke
                || !Consumes(invoke, lookup, slow, merge, merge.Predecessors.IndexOf(slowExit))) continue;
            var exits = merge.NormalSuccessors.ToArray();
            // 各次查找的命中计算可以合成一个带 φ 的块，也可以各占一块（不同槽位的 offset + slot 不能合并时）；入边逐条列出。
            var hits = merge.Predecessors.Where(p => p != slowExit).ToArray();
            if (hits.Distinct().Count() != hits.Length || hits.Any(h => h.Handler is not null || h.IsLandingPad
                || h.NormalSuccessors.ToArray() is not [var hitExit] || hitExit != merge
                || h.Statements.Any(s => s is not (Phi or Define or Jump or Nop)))) continue;
            var hitEdges = hits.SelectMany(h => h.Predecessors.Select((from, side) => (From: from, Hit: h, Side: side))).ToArray();
            if (hitEdges.Length is < 2 or > 16) continue;
            var hit = hits.Length == 1 ? hits[0] : null;
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
                Const { Value: <= ushort.MaxValue } slot when !fast => slot.Value,
                Binary { Op: BinOp.Add, Width: 32, Right: Const { Value: <= ushort.MaxValue } slot } when fast => slot.Value,
                _ => null,
            };
            // 每组：慢路径的入边序号，以及它对应的命中入边序号。任何划分都保持语义，配对只决定下一步能否各自证明为一次查找。
            (int[][] Groups, int[] Mapping)? ByPhi()
            {
                if (hit is null) return null;
                var partition = slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == receiver.Variable);
                var pair = partition is null ? null : merge.Statements.OfType<Phi>().FirstOrDefault(p => p.Sources[merge.Predecessors.IndexOf(slowExit)] == partition.Target);
                var hitPartition = pair is null ? null : hit.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pair.Sources[merge.Predecessors.IndexOf(hit)]);
                var bySlot = hitPartition is null;
                if (bySlot)
                {
                    // 同一接收者的不同接口槽也会共享尾部；以慢路径常量槽和快路径 offset + slot 对齐分支。
                    if (lookup.Arguments[2] is not Use slotUse
                        || slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slotUse.Variable) is not { } slots
                        || slots.Sources.Any(v => Slot(v, false) is null)) return null;
                    var candidates = hit.Statements.OfType<Phi>().Where(p => p.Sources.All(v => Slot(v, true) is { } n
                        && slots.Sources.Any(s => Slot(s, false) == n))).ToArray();
                    if (candidates is not [var fastSlots]) return null;
                    partition = slots;
                    hitPartition = fastSlots;
                }
                var values = partition!.Sources.Select((v, i) => (Value: v, Index: i)).GroupBy(p => p.Value).ToArray();
                if (values.Length != hitEdges.Length) return null;
                var aligned = values.Select(g => bySlot ? Array.FindIndex(hitPartition!.Sources, v => Slot(v, true) == Slot(g.Key, false))
                    : Array.IndexOf(hitPartition!.Sources, g.Key)).ToArray();
                if (aligned.Any(i => i < 0) || aligned.Distinct().Count() != values.Length) return null;
                return (values.Select(g => g.Select(x => x.Index).ToArray()).ToArray(), aligned);
            }
            // 没有接收者或槽位的 φ 可以对齐（如分支各调用一次，或每个槽位各有命中计算）时，哪个查找到达慢路径由支配关系决定。
            (int[][] Groups, int[] Mapping)? ByDominance()
            {
                var dominators = Dominators.Compute(function);
                var loops = hitEdges.Select(e => e.From).ToArray();
                var owners = slow.Predecessors.Select(p => OwnerOf(p, loops, dominators)).ToArray();
                if (owners.Contains(-1)) return null;
                var byOwner = Enumerable.Range(0, loops.Length).Select(i => Enumerable.Range(0, owners.Length).Where(k => owners[k] == i).ToArray()).ToArray();
                if (byOwner.Any(g => g.Length == 0)) return null;
                // 两侧都明确给出槽位时必须一致，矛盾的快慢路径不是同一次查找。
                if (hit is not null && lookup.Arguments[2] is Use slotArgument
                    && slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slotArgument.Variable) is { } slowSlots)
                    foreach (var fastSlots in hit.Statements.OfType<Phi>().Where(p => p.Sources.All(v => Slot(v, true) is not null)))
                        if (byOwner.Select((g, i) => Slot(slowSlots.Sources[g[0]], false) != Slot(fastSlots.Sources[i], true)).Any(differs => differs)) return null;
                return (byOwner, Enumerable.Range(0, loops.Length).ToArray());
            }
            if ((ByPhi() ?? ByDominance()) is not var (groups, mapping)) continue;
            // 同一组的入边在慢路径上取到的值必须相同，才能并成一份副本。
            if (groups.Any(g => slow.Statements.OfType<Phi>().Any(p => g.Select(i => p.Sources[i]).Distinct().Count() != 1))) continue;
            // 槽位是元数据里的 Il2CppMethodSlot（16 位）。
            var slotValid = lookup.Arguments[2] is Const { Value: <= ushort.MaxValue }
                || lookup.Arguments[2] is Use slot && slow.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == slot.Variable) is { } slotPhi
                    && slotPhi.Sources.All(v => definitions.GetValueOrDefault(v) is Const { Value: <= ushort.MaxValue });
            if (!slotValid) continue;
            var shared = hits.Append(slow).Append(merge).Concat(bridges).ToArray();
            var defined = shared.SelectMany(b => b.Statements).SelectMany(Defines).ToHashSet();
            var exit = exits.FirstOrDefault();
            var exitIndex = exit?.Predecessors.IndexOf(merge) ?? -1;
            // 尾部结果只经原出口的对应 φ 入边流出时，复制时按每条路径的变量映射续接；
            // 调用之后还有语句、分支或其他使用时，这些不属于查找尾部，在调用之后切开，只复制到调用为止。
            var invokeEnd = merge.Statements.IndexOf(invoke) + 1;
            var cut = exits.Length > 1 || merge.Statements.Skip(invokeEnd).Any(s => s is Call)
                || function.Blocks.Except(shared).Any(b => b.Statements.Any(s => s is Phi p
                    ? p.Sources.Where((_, i) => b != exit || i != exitIndex).Any(defined.Contains)
                    : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => defined.Contains(u.Variable))));
            var tail = cut ? merge.Statements.Take(invokeEnd).ToArray() : merge.Statements.ToArray();
            if (!cut && exits.Length == 0 && tail.LastOrDefault() is not (Return or Call { Kind: CallKind.TailIndirect })) continue;
            if (slow.Statements.Any(s => s is not (Phi or Define or Call or Jump or Nop))
                || tail.Any(s => s is not (Phi or Define or Call or Jump or Nop or Return))) continue;
            // 切开时只有合流块自己的定义能在调用之后使用（它们支配续接块）；查找两臂的定义到不了合流块之外。
            var armDefined = shared.Where(b => b != merge).SelectMany(b => b.Statements).SelectMany(Defines).ToHashSet();
            if (cut && function.Blocks.Except(shared).Any(b => b.Statements.Any(s => s is Phi p
                ? p.Sources.Any(armDefined.Contains) : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => armDefined.Contains(u.Variable))))) continue;
            var slowEdges = slow.Predecessors.ToArray();
            if (slowEdges.Concat(hitEdges.Select(e => e.From)).Any(p => p.Handler is not null || p.IsLandingPad || shared.Contains(p)
                || p.Successors.Distinct().Count() != p.Successors.Count
                || p.NormalSuccessors.Count() != 1 && p.Statements.LastOrDefault() is not Branch)) continue;
            if (cut)
            {
                exit = CutAfter(function, merge, invoke, tail, Address());
                exitIndex = 0;
            }
            var copies = new List<(Block Slow, Block Hit, Block Merge)>();
            var exitValues = exit?.Statements.OfType<Phi>().ToDictionary(p => p.Target, p => p.Sources[exitIndex]);
            for (var side = 0; side < groups.Length; side++)
            {
                var (slowCopy, slowMap) = Copy(slow, groups[side][0], Address());
                var edge = hitEdges[mapping[side]];
                var (hitCopy, hitMap) = Copy(edge.Hit, edge.Side, Address());
                var mergeAddress = Address();
                var mergeCopy = new Block(mergeAddress) { End = mergeAddress };
                var merged = new Dictionary<Variable, Variable>();
                foreach (var phi in merge.Statements.OfType<Phi>())
                {
                    var target = fresh(phi.Target.Width);
                    merged[phi.Target] = target;
                    var slowValue = phi.Sources[merge.Predecessors.IndexOf(slowExit)];
                    var hitValue = phi.Sources[merge.Predecessors.IndexOf(edge.Hit)];
                    mergeCopy.Statements.Add(new Phi(phi.Address, target, [slowMap.GetValueOrDefault(slowValue, slowValue), hitMap.GetValueOrDefault(hitValue, hitValue)]));
                }
                Append(merge, mergeCopy, merged);
                slowCopy.Statements.RemoveAll(s => s is Jump);
                hitCopy.Statements.RemoveAll(s => s is Jump);
                slowCopy.Statements.Add(new Jump(lookup.Address, mergeCopy.Start));
                hitCopy.Statements.Add(new Jump(edge.Hit.Statements.Last().Address, mergeCopy.Start));
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
                foreach (var source in groups[side]) Redirect(slowEdges[source], slow, copies[side].Slow);
                var edge = hitEdges[mapping[side]];
                Redirect(edge.From, edge.Hit, copies[side].Hit);
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

    /// <summary>间接调用的目标依赖查找结果：经合流 φ、定义和泛型虚方法解析这样的直接调用传递。</summary>
    private static bool Consumes(Call invoke, Call lookup, Block slow, Block merge, int slowEdge)
    {
        var results = lookup.Defines.OfType<Variable>().ToHashSet();
        bool Reads(Stmt statement) => ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => results.Contains(u.Variable));
        foreach (var define in slow.Statements.OfType<Define>().Where(Reads)) results.Add(define.Target);
        results = merge.Statements.OfType<Phi>().Where(p => results.Contains(p.Sources[slowEdge])).Select(p => p.Target).ToHashSet();
        foreach (var statement in merge.Statements.TakeWhile(s => !ReferenceEquals(s, invoke)))
            if (statement is Define define && Reads(define)) results.Add(define.Target);
            else if (statement is Call call && Reads(call)) results.UnionWith(call.Defines.OfType<Variable>());
        return ExprMap.Walk(invoke.Target).OfType<Use>().Any(u => results.Contains(u.Variable));
    }

    /// <summary>
    /// 慢路径的一条入边属于哪个查找循环：沿支配树向上，第一个支配某个循环的块决定归属。
    /// “没有接口”的判断支配自己的循环，循环的退出判断被循环支配。支配多个循环时只有它本身是其中一个才能确定。
    /// </summary>
    private static int OwnerOf(Block from, Block[] loops, Dominators dominators)
    {
        for (var at = from.Index; ; at = dominators.Idom[at])
        {
            var under = Enumerable.Range(0, loops.Length).Where(i => dominators.Dominates(at, loops[i].Index)).ToArray();
            if (under.Length == 1) return under[0];
            if (under.Length > 1) return Array.FindIndex(loops, l => l.Index == at);
            if (at == 0) return -1;
        }
    }

    /// <summary>
    /// 把调用之后的语句移到新的续接块，合流块改为跳到它。合流块的定义在续接块及其后的使用改由续接块入口的 φ 承接：
    /// 目前 φ 只有合流块一条入边，各副本接入时追加来源，原合流块删除时去掉这条入边。
    /// </summary>
    private static Block CutAfter(MachineFunction function, Block merge, Call invoke, Stmt[] tail, ulong address)
    {
        var moved = merge.Statements.Skip(tail.Length).ToArray();
        merge.Statements.RemoveRange(tail.Length, moved.Length);
        var next = new Block(address) { End = merge.End };
        foreach (var successor in merge.Successors)
        {
            next.Successors.Add(successor);
            successor.Predecessors[successor.Predecessors.IndexOf(merge)] = next;
        }
        merge.Successors.Clear();
        var own = tail.SelectMany(Defines).ToHashSet();
        var used = function.Blocks.Where(b => b != merge).SelectMany(b => b.Statements).Concat(moved).SelectMany(s => s is Phi p
            ? p.Sources : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable))
            .Where(own.Contains).Distinct().ToArray();
        foreach (var variable in used)
            next.Statements.Add(new Phi(next.Start, variable, [variable]));
        next.Statements.AddRange(moved);
        if (next.Successors.Count == 1 && next.Statements.LastOrDefault() is not (Jump or Branch))
            next.Statements.Add(new Jump(invoke.Address, next.Successors[0].Start));
        merge.Statements.Add(new Jump(invoke.Address, next.Start));
        MachineFunction.AddEdge(merge, next);
        function.Blocks.Add(next);
        return next;
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
