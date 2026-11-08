using System.Collections.Frozen;
using System.Reflection;
using Cpp2CS.Recovery.Effects;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>
    /// 还原的调用是否写成 callvirt；不能写成调用时为 null。证明说的是这个方法体本身，调用不能分派到别的方法体：
    /// 非虚方法的 callvirt 只多一次判空；接收者是调用方的 this 时写成非虚调用（base.M()）；其他接收者须没有重写。
    /// </summary>
    private bool? Dispatched(MethodRef method, ManagedValue? receiver)
    {
        var definition = method.Method;
        if (definition.IsStatic || definition.Name == ".ctor") return false;
        if (!definition.IsVirtual || (definition.Attributes & MethodAttributes.Final) != 0 || definition.Owner.IsValueType) return true;
        if (receiver is ArgumentValue { Index: -1 }) return false;
        return receiver?.Type is DefinitionRef type && !Overridden(definition, type.Definition) ? true : null;
    }

    /// <summary>从 receiver 类型分派 method 的槽位，可能到达别的方法体：receiver 到方法所在类型之间，或 receiver 的子类里有同槽位的虚方法。</summary>
    private bool Overridden(MethodDef method, TypeDef receiver)
    {
        bool Reaches(TypeDef type, TypeDef ancestor)
        {
            for (TypeRef? at = type.BaseType; at is DefinitionRef definition; at = definition.Definition.BaseType)
                if (ReferenceEquals(definition.Definition, ancestor)) return true;
            return false;
        }
        bool Redefines(TypeDef type) => type.Methods.Any(m => m.IsVirtual && m.Slot == method.Slot);
        for (var at = receiver; !ReferenceEquals(at, method.Owner); at = at.BaseType is DefinitionRef parent ? parent.Definition : method.Owner)
            if (Redefines(at)) return true;
        return types.Model.Types.Any(t => Reaches(t, receiver) && Redefines(t));
    }

    /// <summary>
    /// 模板没有比对到的形参：方法体根本不读它时，任何值的执行结果都相同，写成默认值。
    /// 只比对到一部分路径时不能这样写：返回值的抽象可能用过它而没有留下绑定。引用形参没有默认值。
    /// </summary>
    private ManagedValue? UnreadArgument(InlineMatch match, MethodRef method, int index)
    {
        if (match.Template is not { } template) return null;
        var mentioned = template.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
            .Any(v => v is ArgumentValue argument && argument.Index == index);
        var type = method.Concrete(method.Method.Parameters[index].Type);
        if (mentioned || type is ByRefRef) return null;
        return types.Kind(type) == TypeKind.Struct ? new ComposedValue(type, []) : new ConstantValue(0, type, Width(type));
    }

    /// <summary>
    /// 把证明成立的区域换成一次调用：起点之前的语句保留，随后是调用与到出口的跳转（带出口边上的复制）；
    /// 区域内的块须只从区域内进入、其中定义的值不在区域外使用，之后删去。
    /// </summary>
    private InlineReplacement? PlanReplacement(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> blocks, ulong startBlock, int start, MethodRef method, InlineMatch match, out string failure)
    {
        failure = "区域不能替换";
        if (match.Exit is not { } exit || match.ExitCopies is not { } copies) return null;
        if (match.Rewritten is { } rewritten) (body, blocks) = Rewritten(body, blocks, rewritten);
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
            if ((match.Binding.TryGetValue(i, out var bound) ? Materialize(Input(bound), self, at, match) : UnreadArgument(match, method, i)) is not { } argument) { failure = "实参不能写回调用之前"; return null; }
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
        // 移出区域的语句要在每条路径上都执行：只接受从起点沿无条件跳转到达的块。
        var straight = new HashSet<ulong> { startBlock };
        for (var along = startBlock; blocks[along].Statements[^1] is ManagedJump { Edge.Target: var next } && covered.Contains((along, blocks[along].Statements.Count - 1)) && straight.Add(next); along = next) { }
        if (match.Interleaved.Any(p => !straight.Contains(p.Block))) { failure = "移出区域的语句不在起点的直线路径上"; return null; }
        if (match.Interleaved.Any(p => p.Effects > 0 && p.Effects < match.Effects)) { failure = "夹在调用之间的写入不能移出区域"; return null; }
        var hoisted = match.Interleaved.Where(p => p.Effects == 0).Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        var sunk = match.Interleaved.Where(p => p.Effects > 0).Select(p => blocks[p.Block].Statements[p.Index]).ToArray();
        if (hoisted.Concat(sunk).SelectMany(ReadValues).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => match.Defined.ContainsKey(l.Variable)))
        { failure = "移出区域的写入依赖区域内定义的局部"; return null; }
        // 提到调用之前的赋值不能改写调用要用的局部。
        var hoistedTargets = hoisted.OfType<ManagedAssignment>().Select(a => a.Target.Variable).ToHashSet();
        if (hoistedTargets.Count > 0 && arguments.Concat(receiver is null ? [] : [receiver]).Concat(exitCopies.Select(c => c.Value)).SelectMany(ManagedValues.Walk)
            .OfType<LocalValue>().Any(l => hoistedTargets.Contains(l.Variable)))
        { failure = "提到调用之前的赋值改写了调用要用的局部"; return null; }
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
        // 多个内联点可以共享尾部（编译器合并了相同的代码）：这个入口改写成调用后不再进入它，仍被外部入口使用的块及其后继原样留下，轮到那些入口时再证明。
        var shared = new HashSet<ulong>();
        var pending = new Queue<ulong>(body.Blocks.Where(b => !region.Contains(b.Address))
            .SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges)).Select(e => e.Target).Where(internalBlocks.Contains));
        while (pending.TryDequeue(out var address))
        {
            if (!shared.Add(address)) continue;
            foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges).Where(e => internalBlocks.Contains(e.Target)))
                pending.Enqueue(edge.Target);
        }
        // 不会抛出的块可在 try 外（原生调用点表不覆盖它们）；可能抛出的语句须保留起点的异常上下文。
        // 只看显式抛出的语句：隐式的判空和边界检查在原生里已经由判断排除，真会抛的话调用点表就覆盖它了。
        // 起点不在 try 里而这些语句都在时，调用要进 try：起点块留下的语句都不抛出，把这个块并入 try 不改变它们。
        var raising = region.Where(b => match.Raising.Contains(b) && blocks[b].Statements.Any(s => s is ManagedCall or ManagedThrow or ManagedCheck)).ToArray();
        var kept = blocks[startBlock].Statements.Take(start)
            .Concat(!match.Returns && exit.Index > 0 ? blocks[exit.Block].Statements.Skip(exit.Index) : []).ToArray();
        var joined = new HashSet<ManagedRegion>(ReferenceEqualityComparer.Instance);
        foreach (var r in body.Regions)
        {
            if (internalBlocks.Contains(r.HandlerEntry) || raising.Any(b => r.Handler.Contains(b) != r.Handler.Contains(startBlock)))
            { failure = "区域跨越异常边界"; return null; }
            if (raising.All(b => r.Try.Contains(b) == r.Try.Contains(startBlock))) continue;
            if (r.Try.Contains(startBlock) || !raising.All(r.Try.Contains) || kept.Any(s => ManagedEffects.Statement(s).Exceptions != ExceptionEffect.None))
            { failure = "区域跨越异常边界"; return null; }
            joined.Add(r);
        }
        internalBlocks.ExceptWith(shared);
        covered.RemoveWhere(p => shared.Contains(p.Block));
        // 区域内定义的值不在区域外使用。共享块里的读取，到达的值来自其他入口：这个入口不再进入，但其他入口要真的定义它。
        var outsideAll = body.Blocks.SelectMany(b => b.Statements.Select((s, i) => (b.Address, i, s)))
            .Where(p => !covered.Contains((p.Address, p.i)) && !(!match.Returns && p.Address == exit.Block && exit.Index > 0 && p.i < exit.Index)).ToArray();
        var redefined = outsideAll.SelectMany(p => (p.s is ManagedAssignment assigned ? new[] { assigned.Target.Variable } : [])
            .Concat(p.s is ManagedCall { Result: { } called } ? [called.Variable] : [])
            .Concat(ManagedValues.Edges(p.s).SelectMany(e => e.Copies).Select(c => c.Target.Variable))).ToHashSet();
        var outside = outsideAll.Select(p => (p.Address, p.i, s: p.s,
            Reads: ReadValues(p.s).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Where(l => !shared.Contains(p.Address) || !redefined.Contains(l.Variable)).ToArray())).ToArray();
        var defined = match.Defined.Keys.Where(v => (match.Result is null || !v.Equals(match.Result.Variable))
            && copies.All(c => !c.Target.Variable.Equals(v))).ToHashSet();
        if (match.Continuation is { } edges)
            defined.ExceptWith(edges.Taken.Copies.Concat(edges.Fallthrough.Copies).Select(c => c.Target.Variable));
        var escapingValues = outside.SelectMany(p => p.Reads).Select(l => l.Variable).Where(defined.Contains).ToHashSet();
        var savedCopies = InlineCopies(body, blocks, startBlock, start, match, escapingValues, self);
        defined.ExceptWith(savedCopies.Select(a => a.Target.Variable));
        foreach (var (_, _, statement, reads) in outside)
            if (reads.FirstOrDefault(l => defined.Contains(l.Variable)) is { } escaping)
                { failure = $"区域内定义的值 {escaping.Variable} 在区域外 0x{statement.Address:x} 使用"; return null; }

        if (ArrivalCopies(body, match, blocks, region, at, out failure) is not { } arrivals) return null;
        if (Dispatched(method, receiver) is not { } dispatched) { failure = $"{method.Method.Name} 可能被重写，调用不一定到这个方法体"; return null; }
        var call = new ManagedCall(at, new ManagedInvocation(method, receiver, arguments, dispatched), match.Result) { Inlined = true };
        if (match.Effects == 0 && match.Ends.All(e => e.State is { Stores.Count: 0 })) pureInlines.Add(call);
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
            if (exit.Block != startBlock && !shared.Contains(exit.Block)) internalBlocks.Add(exit.Block);
        }
        var form = match.Continuation is not null ? "branch" : match.ResultAtUses is not null ? "uses" : match.Returns ? "return" : "exit";
        if (copies.Count > 0) form += "+copies";
        var proof = new Cpp2CS.Diagnostics.RuleTrace(ProofRule, at, Cpp2CS.Diagnostics.RewriteStatus.Applied,
            string.Join("+", match.Forms.Prepend(form)), $"{method.Method.Owner.FullName}.{method.Method.Name}", null);
        return new InlineReplacement(startBlock, replacement.ToArray(), internalBlocks.ToFrozenSet(), match.Rewritten) { JoinedTry = joined, Proof = proof };
    }
}
