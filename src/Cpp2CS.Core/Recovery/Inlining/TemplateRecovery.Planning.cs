using System.Collections.Frozen;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>
    /// 把证明成立的区域换成一次调用：起点之前的语句保留，随后是调用与到出口的跳转（带出口边上的复制）；
    /// 区域内的块须只从区域内进入、其中定义的值不在区域外使用，之后删去。
    /// </summary>
    private InlineReplacement? PlanReplacement(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks, ulong startBlock, int start, MethodRef method, InlineMatch match, out string failure)
    {
        failure = "区域不能替换";
        if (match.Exit is not { } exit || match.ExitCopies is not { } copies) return null;
        var at = blocks[startBlock].Statements[start].Address;
        // 静态方法没有接收者；实例方法的 this 须在比对中绑定。
        ManagedValue? self = null;
        if (!method.Method.IsStatic && !match.Binding.TryGetValue(-1, out self)) { failure = "模板没有用到 this"; return null; }
        // 区域之前已保存的值沿用原局部，不把它重新展开为更晚时刻的内存读取。
        ManagedValue Input(ManagedValue value)
        {
            foreach (var available in match.Inputs)
                if (SameTerm(value, available.Value)) return available.Local;
            return MapTerm(value, Input);
        }
        // 下面按换成已保存局部之后的项查询。
        match.EarlyReads.UnionWith(match.EarlyReads.Select(Input).ToArray());
        if (self is not null) self = Input(self);
        var parameters = method.Method.Parameters.Count;
        var arguments = new ManagedValue[parameters];
        for (var i = 0; i < parameters; i++)
            if (!match.Binding.TryGetValue(i, out var bound) || Materialize(Input(bound), self, at, match) is not { } argument) { failure = "实参不能写回调用之前"; return null; }
            else arguments[i] = argument;
        var exitCopies = new List<ManagedCopy>();
        foreach (var (target, value) in copies)
            if (Materialize(Input(value), self, at, match) is { } materialized) exitCopies.Add(new ManagedCopy(target, materialized));
            else { failure = $"出口复制 {target.Variable} 不能写回"; return null; }
        ManagedValue? receiver = null;
        if (self is not null && (receiver = Materialize(self, self, at, match)) is null) { failure = "接收者不能写回"; return null; }
        if (receiver is not null && method.DeclaringType is DefinitionRef { Definition.IsValueType: true } && receiver.Type is not ByRefRef)
        {
            if (receiver is not (LocalValue or FieldValue or StaticFieldValue or ArrayElementValue)) { failure = "值类型接收者不可取址"; return null; }
            receiver = new AddressValue(receiver);
        }
        var covered = match.Covered.ToHashSet();
        // 模板写入之间的调用方写入与模板无关，移到调用之前或之后；它们原样保留，不能依赖区域内定义的局部。
        if (match.Interleaved.Any(p => p.Block != startBlock)) { failure = "移出区域的写入不在起点块"; return null; }
        if (match.Interleaved.Any(p => p.Effects > 0 && p.Effects < match.Effects)) { failure = "夹在调用之间的写入不能移出区域"; return null; }
        var hoisted = match.Interleaved.Where(p => p.Effects == 0).Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        var sunk = match.Interleaved.Where(p => p.Effects > 0).Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        if (hoisted.Concat(sunk).SelectMany(ReadValues).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => match.Defined.ContainsKey(l.Variable)))
        { failure = "移出区域的写入依赖区域内定义的局部"; return null; }
        covered.UnionWith(match.Interleaved.Select(p => (p.Block, p.Index)));
        var internalBlocks = covered.Select(c => c.Block).Where(b => b != startBlock).Distinct().ToHashSet();
        if (match.Continuation is { } continuation)
        {
            internalBlocks.Remove(continuation.Taken.Target);
            internalBlocks.Remove(continuation.Fallthrough.Target);
        }
        // 出口在区域内某块的中间时，该块余下的语句接在调用之后。
        if (!match.Returns && exit.Index > 0 && exit.Block != startBlock && !internalBlocks.Contains(exit.Block)) { failure = "出口不在区域内"; return null; }
        if (!match.Returns && exit.Index == 0) internalBlocks.Remove(exit.Block);
        foreach (var address in internalBlocks)
        {
            var count = blocks[address].Statements.Count;
            var whole = Enumerable.Range(0, count).All(i => covered.Contains((address, i)) || !match.Returns && address == exit.Block && i >= exit.Index);
            if (!whole) { failure = "区域内的块含有区域外的语句"; return null; }
        }
        if (Enumerable.Range(start, blocks[startBlock].Statements.Count - start).Any(i => !covered.Contains((startBlock, i)) && !(!match.Returns && startBlock == exit.Block && i >= exit.Index))) { failure = "起点块含有区域外的语句"; return null; }
        var region = internalBlocks.Append(startBlock).ToHashSet();
        // 多个内联点可以共享判断尾部；保留仍被外部入口使用的尾部及其后继（只有控制转移的块，留下来不改变语义）。
        var shared = new HashSet<ulong>();
        var pending = new Queue<ulong>(body.Blocks.Where(b => !region.Contains(b.Address))
            .SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)).Select(e => e.Target).Where(internalBlocks.Contains));
        while (pending.TryDequeue(out var address))
        {
            if (!shared.Add(address)) continue;
            if (blocks[address].Statements.Any(s => s is not (ManagedBranch or ManagedJump or ManagedReturn)))
            { failure = "区域内的块从区域外进入"; return null; }
            foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges).Where(e => internalBlocks.Contains(e.Target)))
                pending.Enqueue(edge.Target);
        }
        // 不会抛出的块可在 try 外（原生调用点表不覆盖它们）；可能抛出的语句须保留起点的异常上下文。
        if (body.Regions.Any(r => internalBlocks.Contains(r.HandlerEntry)
            || region.Any(b => match.Raising.Contains(b) && (r.Try.Contains(b) != r.Try.Contains(startBlock) || r.Handler.Contains(b) != r.Handler.Contains(startBlock)))))
        { failure = "区域跨越异常边界"; return null; }
        internalBlocks.ExceptWith(shared);
        covered.RemoveWhere(p => shared.Contains(p.Block));
        // 区域内定义的值不在区域外使用。
        var outside = body.Blocks.SelectMany(b => b.Statements.Select((s, i) => (b.Address, i, s)))
            .Where(p => !covered.Contains((p.Address, p.i)) && !(!match.Returns && p.Address == exit.Block && exit.Index > 0 && p.i < exit.Index));
        var defined = match.Defined.Keys.Where(v => (match.Result is null || !v.Equals(match.Result.Variable))
            && copies.All(c => !c.Target.Variable.Equals(v))).ToHashSet();
        if (match.Continuation is { } edges)
            defined.ExceptWith(edges.Taken.Copies.Concat(edges.Fallthrough.Copies).Select(c => c.Target.Variable));
        var escapingValues = outside.SelectMany(p => ReadValues(p.s)).SelectMany(ManagedValues.Walk).OfType<LocalValue>()
            .Select(l => l.Variable).Where(defined.Contains).ToHashSet();
        var savedCopies = InlineCopies(body, blocks, startBlock, start, match, escapingValues, self);
        defined.ExceptWith(savedCopies.Select(a => a.Target.Variable));
        foreach (var (_, _, statement) in outside)
            if (ReadValues(statement).SelectMany(ManagedValues.Walk).OfType<LocalValue>().FirstOrDefault(l => defined.Contains(l.Variable)) is { } escaping)
                { failure = $"区域内定义的值 {escaping.Variable} 在区域外 0x{statement.Address:x} 使用"; return null; }

        if (ArrivalCopies(body, match, blocks, at, out failure) is not { } arrivals) return null;
        var call = new ManagedCall(at, new ManagedInvocation(method, receiver, arguments, !method.Method.IsStatic && method.Method.Name != ".ctor"), match.Result) { Inlined = true };
        var replacement = blocks[startBlock].Statements.Take(start).Concat(hoisted).Concat(savedCopies).Concat(arrivals).Append(call).Concat(sunk).ToList();
        if (match.Returns) replacement.Add(new ManagedReturn(at, match.Result));
        if (match.Continuation is { } branch)
        {
            ManagedEdge? MaterializeEdge(ManagedEdge edge)
            {
                var converted = new List<ManagedCopy>();
                foreach (var copy in edge.Copies)
                    if (Materialize(Input(copy.Value), self, at, match) is { } value) converted.Add(copy with { Value = value });
                    else return null;
                return edge with { Copies = converted };
            }
            if (MaterializeEdge(branch.Taken) is not { } taken || MaterializeEdge(branch.Fallthrough) is not { } fallthrough)
            { failure = "条件出口复制不能写回"; return null; }
            if (Materialize(Input(branch.Condition), self, at, match) is not { } condition) { failure = "条件出口的谓词不能写回"; return null; }
            replacement.Add(branch with { Address = at, Condition = condition, Taken = taken, Fallthrough = fallthrough });
        }
        else if (!match.Returns && exit.Index == 0)
            replacement.Add(new ManagedJump(call.Address, new ManagedEdge(exit.Block, exitCopies)));
        else if (!match.Returns)
        {
            replacement.AddRange(exitCopies.Select(c => new ManagedAssignment(call.Address, c.Target, c.Value)));
            replacement.AddRange(blocks[exit.Block].Statements.Skip(exit.Index));
            if (exit.Block != startBlock) internalBlocks.Add(exit.Block);
        }
        return new InlineReplacement(startBlock, replacement.ToArray(), internalBlocks.ToFrozenSet());
    }
}
