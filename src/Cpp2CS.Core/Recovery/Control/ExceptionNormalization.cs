using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// C++ 异常机制到 IL 异常语义的规范化。IL2CPP 的托管异常总以 Il2CppExceptionWrapper 抛出：落地块中 selector 对托管异常
/// 恒为 LSDA 里 catch(Il2CppExceptionWrapper&amp;) 动作的序号（没有 catch 动作时为 0，即只做清理），其余分支对 IL 不可达。
/// 规范化由三部分组成：
/// <list type="bullet">
/// <item>不产生托管异常的抛出点没有异常边：wrapper 没有析构回调时，结束 catch 不会再次抛出。</item>
/// <item>落地链收缩：落地块之后只传递值的直线路径在 IL 中没有对应，异常边直接指向链的目标（<see cref="ContractLandingChains"/>）。</item>
/// <item>没有托管效果的处理体：只取异常后终止（noexcept 中再次抛出）或继续向外展开，IL 中异常照常向外传播，指向它的异常边删去。</item>
/// </list>
/// </summary>
internal static class ExceptionNormalization
{
    public static void Run(MachineFunction function, bool wrapperWithoutDestructor)
    {
        if (!function.Blocks.Any(b => b.IsLandingPad)) return;
        foreach (var pad in function.Blocks.Where(b => b.IsLandingPad))
        {
            var filter = function.Range.ExceptionRegions.Where(r => r.LandingPad == pad.Start).SelectMany(r => r.Actions)
                .FirstOrDefault(a => a.Kind == "typed-catch")?.Filter ?? 0;
            for (var i = 0; i < pad.Statements.Count; i++)
                if (pad.Statements[i] is Define { Value: Intrinsic { Name: "eh_selector" } } selector)
                    pad.Statements[i] = selector with { Value = Expr.C(unchecked((ulong)filter), selector.Value.Width) };
        }
        foreach (var block in function.Blocks.ToArray())
            if (block.Handler is { } pad && (Inert(pad) || wrapperWithoutDestructor && EndsCatchOnly(block)))
                MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
        if (wrapperWithoutDestructor)
            foreach (var block in function.Blocks)
                block.Statements.RemoveAll(s => s is Call { Op.Kind: OpKind.EndCatch, Defines.Length: 0 });
        // selector 常量先折叠分支，再收缩落地链：收缩把链上的常量移到各抛出点，之后不再参与折叠。
        Machine.Ssa.Lowering.Cleanup(function);
        while (FoldBranches(function))
            Machine.Ssa.Lowering.Cleanup(function);
        ContractLandingChains(function);
        // 收缩后成为落地块的目标可能只是终止或继续展开。
        foreach (var block in function.Blocks.ToArray())
            if (block.Handler is { } pad && Inert(pad))
                MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
        var errors = Machine.Ssa.Lowering.Cleanup(function);
        if (errors.Count > 0) throw new InvalidOperationException($"异常入口规范化后 SSA 不成立：{errors[0]}");
    }

    /// <summary>块中的调用都是结束 catch。</summary>
    private static bool EndsCatchOnly(Block block) => block.Statements.OfType<Call>().Any(c => c.Op?.Kind == OpKind.EndCatch)
        && block.Statements.OfType<Call>().All(c => c.Op?.Kind == OpKind.EndCatch);

    /// <summary>
    /// 没有托管效果的处理体：只取异常与 selector、装载常量，然后调用 std::terminate（noexcept 析构中再次抛出），
    /// 或只取异常后继续向外展开。必须看到实际的终止或展开调用。
    /// </summary>
    private static bool Inert(Block pad) =>
        pad.Statements.OfType<Call>().Any(c => c.Op?.Kind == OpKind.Terminate)
            && pad.Statements.All(s => s is Nop or Define { Value: Const or Intrinsic { Name: "eh_exception" or "eh_selector" } }
                or Call { Op.Kind: OpKind.Terminate or OpKind.BeginCatch })
        || pad.Statements.OfType<Call>().Any(c => c.Op?.Kind == OpKind.ResumeUnwind)
            && pad.Statements.All(s => s is Nop or Define { Value: Intrinsic { Name: "eh_exception" } } or Call { Op.Kind: OpKind.ResumeUnwind });

    /// <summary>落地链上的语句：φ、跳转、空语句，常量或异常值的定义。</summary>
    private static bool Passing(Stmt statement) => statement is Phi or Jump or Nop or Define { Value: Const or Intrinsic { Name: "eh_exception" } };

    /// <summary>链上的值经某条异常入边到达目标时是什么：链外的变量、要在抛出点之前定义的常量，或异常值。</summary>
    private abstract record Arrival;
    private sealed record Outside(Variable? Variable) : Arrival;
    private sealed record Constant(Define Definition) : Arrival;
    private sealed record Thrown(Define Definition) : Arrival;

    private sealed record Chain(Block[] Blocks, Block[] Throwers, Arrival[][] Values);

    /// <summary>
    /// 落地链：从落地块起，只含 φ、跳转、空语句与常量或异常值定义的直线路径，后续块只从前一块进入，止于第一个其他块（目标）。
    /// clang 为调用点生成的跳板、在共享处理体之前装载常量的入口都是这样的链。收缩后抛出点的异常边直接指向目标：
    /// 链上的 φ 按每条异常入边代入来源，常量在抛出点之前定义，异常值在目标入口取得。
    /// 链上的定义只能作为目标 φ 的输入；目标中由异常值组成的 φ 要求目标的每个前驱都是给出异常值的链，否则不收缩。
    /// </summary>
    private static void ContractLandingChains(MachineFunction function)
    {
        var nextTemp = function.Blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            { Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines.OfType<Variable>(), _ => [] })
            .Concat(function.Dead.Select(d => d.Define.Target))
            .Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
        foreach (var target in function.Blocks.ToArray())
        {
            if (!function.Blocks.Contains(target)) continue;
            var phis = target.Statements.TakeWhile(s => s is Phi).Cast<Phi>().ToArray();
            var chains = new List<(int Predecessor, Chain Chain)>();
            for (var k = 0; k < target.Predecessors.Count; k++)
                if (Trace(function, target, k, phis) is { } chain) chains.Add((k, chain));
            if (chains.Count == 0) continue;
            // 由异常值组成的 φ：目标的每个前驱都是链，且在每个抛出点都给出异常值。
            var thrown = Enumerable.Range(0, phis.Length).Where(i => chains.Any(c => c.Chain.Values.Any(v => v[i] is Thrown))).ToArray();
            if (thrown.Length > 0 && (chains.Count != target.Predecessors.Count
                || thrown.Any(i => chains.Any(c => c.Chain.Values.Any(v => v[i] is not Thrown))))) continue;
            foreach (var (_, chain) in chains)
                MachineFunction.RemoveEdge(chain.Blocks[^1], target);
            var ordinary = Enumerable.Range(0, phis.Length).Except(thrown).ToArray();
            if (thrown.Length > 0)
            {
                var entries = thrown.Select(i => (Stmt)new Define(phis[i].Address, phis[i].Target, ((Thrown)chains[0].Chain.Values[0][i]).Definition.Value)).ToArray();
                target.Statements.RemoveAll(s => s is Phi phi && thrown.Any(i => phis[i].Target == phi.Target));
                target.Statements.InsertRange(ordinary.Length, entries);
            }
            foreach (var (_, chain) in chains)
            {
                for (var t = 0; t < chain.Throwers.Length; t++)
                {
                    var thrower = chain.Throwers[t];
                    var insert = thrower.Statements.FindLastIndex(s => s is Call);
                    if (insert < 0) insert = thrower.Statements.Count;
                    var sources = new Variable[ordinary.Length];
                    for (var o = 0; o < ordinary.Length; o++)
                        switch (chain.Values[t][ordinary[o]])
                        {
                            case Outside outside: sources[o] = outside.Variable!; break;
                            case Constant constant:
                                var fresh = new Variable(new Storage(Bank.Temp, nextTemp++, constant.Definition.Target.Width), 1);
                                thrower.Statements.Insert(insert++, new Define(constant.Definition.Address, fresh, constant.Definition.Value));
                                sources[o] = fresh;
                                break;
                        }
                    MachineFunction.RemoveEdgeAt(thrower, thrower.Successors.Count - 1);
                    MachineFunction.AddEdge(thrower, target);
                    thrower.Handler = target;
                    for (var o = 0; o < ordinary.Length; o++)
                    {
                        var phi = (Phi)target.Statements[o];
                        target.Statements[o] = phi with { Sources = [.. phi.Sources, sources[o]] };
                    }
                }
                for (var b = chain.Blocks.Length - 1; b > 0; b--)
                    MachineFunction.RemoveEdge(chain.Blocks[b - 1], chain.Blocks[b]);
                foreach (var block in chain.Blocks) function.Blocks.Remove(block);
            }
            target.IsLandingPad = true;
        }
        function.Renumber();
    }

    /// <summary>目标第 k 个前驱所在的落地链及其值经每个抛出点到达目标时的来源；不是可收缩的链时为 null。</summary>
    private static Chain? Trace(MachineFunction function, Block target, int k, Phi[] phis)
    {
        var blocks = new List<Block> { target.Predecessors[k] };
        while (true)
        {
            var current = blocks[0];
            if (current == target || current.Handler is not null || !current.Statements.All(Passing)
                || current.Successors is not [var next] || next != (blocks.Count > 1 ? blocks[1] : target)) return null;
            if (current.IsLandingPad && current.Predecessors.Count > 0 && current.Predecessors.All(p => p.Handler == current)) break;
            if (blocks.Count >= 8 || current.Predecessors is not [var previous] || previous.Successors is not [_] || blocks.Contains(previous)) return null;
            blocks.Insert(0, previous);
        }
        var pad = blocks[0];
        var throwers = pad.Predecessors.ToArray();
        var definitions = new Dictionary<Variable, Stmt>();
        foreach (var statement in blocks.SelectMany(b => b.Statements))
            switch (statement)
            {
                case Define d: definitions[d.Target] = d; break;
                case Phi p: definitions[p.Target] = p; break;
            }
        // 链上的定义只能作为目标 φ 在这条入边上的输入。
        foreach (var block in function.Blocks.Where(b => !blocks.Contains(b)))
            foreach (var statement in block.Statements)
            {
                var used = statement is Phi phi
                    ? phi.Sources.Where((v, j) => v is not null && !(block == target && j == k))
                    : ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
                if (used.Any(v => v is not null && definitions.ContainsKey(v))) return null;
            }
        // 落地块的 φ 按抛出点取来源；链上后续块只有一个前驱，其 φ 等于唯一来源。
        Arrival? Arrive(Variable? value, int thrower)
        {
            for (var step = 0; step <= blocks.Count; step++)
            {
                if (value is null || !definitions.TryGetValue(value, out var definition)) return new Outside(value);
                switch (definition)
                {
                    case Define { Value: Const } constant: return new Constant(constant);
                    case Define exception: return new Thrown(exception);
                    case Phi phi: value = pad.Statements.Contains(phi) ? phi.Sources[thrower] : phi.Sources[0]; break;
                }
            }
            return null;
        }
        var values = new Arrival[throwers.Length][];
        for (var t = 0; t < throwers.Length; t++)
        {
            values[t] = new Arrival[phis.Length];
            for (var i = 0; i < phis.Length; i++)
                if (Arrive(phis[i].Sources[k], t) is { } arrival) values[t][i] = arrival;
                else return null;
        }
        return new Chain(blocks.ToArray(), throwers, values);
    }

    /// <summary>条件为常量的分支改为跳转，删去不可达的边。</summary>
    private static bool FoldBranches(MachineFunction function)
    {
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch branch || Fold.Simplify(branch.Condition) is not Const c) continue;
            var (kept, dropped) = c.Value != 0 ? (branch.Target, branch.Fallthrough) : (branch.Fallthrough, branch.Target);
            block.Statements[^1] = new Jump(branch.Address, kept);
            if (kept != dropped && block.Successors.FirstOrDefault(s => s.Start == dropped) is { } dead)
                MachineFunction.RemoveEdge(block, dead);
            changed = true;
        }
        if (changed) function.Renumber();
        return changed;
    }
}
