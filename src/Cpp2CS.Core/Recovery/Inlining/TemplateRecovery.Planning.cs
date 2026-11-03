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
        if (self is not null) self = Input(self);
        var parameters = method.Method.Parameters.Count;
        var arguments = new ManagedValue[parameters];
        for (var i = 0; i < parameters; i++)
            if (!match.Binding.TryGetValue(i, out var bound) || Materialize(Input(bound), self, at) is not { } argument) { failure = "实参不能写回调用之前"; return null; }
            else arguments[i] = argument;
        var exitCopies = new List<ManagedCopy>();
        foreach (var (target, value) in copies)
            if (Materialize(Input(value), self, at) is { } materialized) exitCopies.Add(new ManagedCopy(target, materialized));
            else { failure = "出口复制不能写回"; return null; }
        ManagedValue? receiver = null;
        if (self is not null && (receiver = Materialize(self, self, at)) is null) { failure = "接收者不能写回"; return null; }
        if (receiver is not null && method.DeclaringType is DefinitionRef { Definition.IsValueType: true } && receiver.Type is not ByRefRef)
        {
            if (receiver is not (LocalValue or FieldValue or StaticFieldValue or ArrayElementValue)) { failure = "值类型接收者不可取址"; return null; }
            receiver = new AddressValue(receiver);
        }
        var covered = match.Covered;
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
        foreach (var other in body.Blocks.Where(b => !region.Contains(b.Address)))
            if (other.Statements.SelectMany(ManagedValues.Edges).Any(e => internalBlocks.Contains(e.Target))) { failure = "区域内的块从区域外进入"; return null; }
        // 纯跳转与局部复制不会抛出异常，尾部这类块可在 try 外；实际效果仍须保留起点的异常上下文。
        bool Inert(ulong block) => blocks[block].Statements.All(s => s is ManagedJump jump
            && jump.Edge.Copies.All(c => c.Value is LocalValue or ArgumentValue or ConstantValue));
        if (body.Regions.Any(r => internalBlocks.Contains(r.HandlerEntry)
            || region.Any(b => !Inert(b) && (r.Try.Contains(b) != r.Try.Contains(startBlock) || r.Handler.Contains(b) != r.Handler.Contains(startBlock)))))
        { failure = "区域跨越异常边界"; return null; }
        // 区域内定义的值不在区域外使用。
        var outside = body.Blocks.SelectMany(b => b.Statements.Select((s, i) => (b.Address, i, s)))
            .Where(p => !covered.Contains((p.Address, p.i)) && !(!match.Returns && p.Address == exit.Block && exit.Index > 0 && p.i < exit.Index));
        var defined = match.Defined.Keys.Where(v => (match.Result is null || !v.Equals(match.Result.Variable))
            && (match.ResultStorage is null || !v.Equals(match.ResultStorage.Variable))).ToHashSet();
        var escapingValues = outside.SelectMany(p => ReadValues(p.s)).SelectMany(ManagedValues.Walk).OfType<LocalValue>()
            .Select(l => l.Variable).Where(defined.Contains).ToHashSet();
        var savedCopies = InlineCopies(body, blocks, startBlock, start, match, escapingValues);
        defined.ExceptWith(savedCopies.Select(a => a.Target.Variable));
        foreach (var (_, _, statement) in outside)
            if (ReadValues(statement).SelectMany(ManagedValues.Walk).OfType<LocalValue>().FirstOrDefault(l => defined.Contains(l.Variable)) is { } escaping)
                { failure = $"区域内定义的值 {escaping.Variable} 在区域外 0x{statement.Address:x} 使用"; return null; }
        if (copies.Any(c => defined.Contains(c.Target.Variable))) { failure = "区域内定义的值在区域外使用"; return null; }

        var call = new ManagedCall(at, new ManagedInvocation(method, receiver, arguments, !method.Method.IsStatic && method.Method.Name != ".ctor"), match.Result, match.Returns) { Inlined = true };
        var replacement = blocks[startBlock].Statements.Take(start).Concat(savedCopies).Append(call).ToList();
        if (match.Continuation is { } branch)
        {
            ManagedEdge? MaterializeEdge(ManagedEdge edge)
            {
                var converted = new List<ManagedCopy>();
                foreach (var copy in edge.Copies)
                    if (Materialize(Input(copy.Value), self, at) is { } value) converted.Add(copy with { Value = value });
                    else return null;
                return edge with { Copies = converted };
            }
            if (MaterializeEdge(branch.Taken) is not { } taken || MaterializeEdge(branch.Fallthrough) is not { } fallthrough)
            { failure = "条件出口复制不能写回"; return null; }
            replacement.Add(branch with { Address = at, Taken = taken, Fallthrough = fallthrough });
        }
        else if (!match.Returns && exit.Index == 0)
            replacement.Add(new ManagedJump(call.Address, new ManagedEdge(exit.Block, exitCopies)));
        else if (!match.Returns)
        {
            if (exitCopies.Count > 0) { failure = "出口在块中间且带复制"; return null; }
            replacement.AddRange(blocks[exit.Block].Statements.Skip(exit.Index));
            if (exit.Block != startBlock) internalBlocks.Add(exit.Block);
        }
        return new InlineReplacement(startBlock, replacement.ToArray(), internalBlocks.ToFrozenSet());
    }
}
