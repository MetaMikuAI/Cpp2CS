using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>将没有独立栈局部的原生闭包展开到调用点，保留调用者的异常边和 SSA 输入。</summary>
internal static class OutlinedCallInlining
{
    public static bool Run(MachineFunction caller, Block block, Call call, MachineFunction callee)
    {
        var index = block.Statements.IndexOf(call);
        if (index < 0 || index < block.Statements.Count - 1 && block.Handler is not null) return false;
        var split = index < block.Statements.Count - 1;
        var continuation = split ? new Block(Math.Max(NameSupply.JoinedEdgeBase, caller.Blocks.Max(b => b.Start) + 1))
            { End = block.End, Statements = block.Statements.Skip(index + 1).ToList() }
            : block.NormalSuccessors.ToArray() is [var successorBlock] ? successorBlock : null;
        if (continuation is null || continuation == block.Handler || callee.EntryBlock.Predecessors.Count != 0
            || callee.Blocks.Any(b => b.Handler is not null || b.IsLandingPad)
            || callee.Blocks.SelectMany(b => b.Statements).Any(s => s is Assign or Opaque or IndirectJump
                || s is Call { Kind: CallKind.Tail or CallKind.TailIndirect })) return false;
        var all = caller.Blocks.SelectMany(b => b.Statements).ToArray();
        var used = all.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
            .Concat(all.OfType<Phi>().SelectMany(p => p.Sources)).ToHashSet();
        var outputs = call.Defines.Where(v => v is not null && used.Contains(v)).ToArray();
        if (outputs.Length > 1 || outputs.Length == 1 && !split && continuation.Predecessors.Count != 1) return false;
        var output = outputs.SingleOrDefault();
        var saved = callee.Blocks.SelectMany(b => b.Statements).OfType<Store>()
            .Where(s => s is { Target: FrameAddress, Value: Use { Variable.Version: 0, Variable.Storage.Bank: Bank.Gpr } u }
                && u.Variable.Storage.Index is >= 19 and <= 30).ToHashSet();
        var statements = callee.Blocks.SelectMany(b => b.Statements).Where(s => s is not Store store || !saved.Contains(store)).ToArray();
        if (statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).Any(e => e is FrameAddress)
            || statements.OfType<Return>().Any(r => (r.Value is null) != (output is null) || r.Buffer is not null || r.Pieces.Length != 0)
            || output is not null && !statements.OfType<Return>().Any()) return false;
        var inputs = call.ArgumentsBySource();
        var variables = statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable)
            .Concat(statements.OfType<Phi>().SelectMany(p => p.Sources)).Distinct().ToArray();
        if (variables.Any(v => v.Version < 0 || v.Version == 0 && !inputs.ContainsKey(v.Storage))) return false;

        var versions = all.SelectMany(Defined).Concat(used).GroupBy(v => v.Storage).ToDictionary(g => g.Key, g => g.Max(v => v.Version));
        var renamed = statements.SelectMany(Defined).Distinct().ToDictionary(v => v, v =>
        {
            var next = versions.GetValueOrDefault(v.Storage) + 1;
            versions[v.Storage] = next;
            return new Variable(v.Storage, next);
        });
        // 入口值也使用显式定义，保证 phi 的逐前驱输入仍是变量。
        var bindings = new List<Stmt>();
        foreach (var input in variables.Where(v => v.Version == 0))
        {
            var next = versions.GetValueOrDefault(input.Storage) + 1;
            versions[input.Storage] = next;
            var target = new Variable(input.Storage, next);
            renamed[input] = target;
            bindings.Add(new Define(call.Address, target, inputs[input.Storage]));
        }
        Expr Map(Expr expression) => Fold.Simplify(ExprMap.Map(expression,
            e => e is Use u ? new Use(renamed[u.Variable], u.Width) : null));
        var label = Math.Max(NameSupply.JoinedEdgeBase, Math.Max(continuation.Start, caller.Blocks.Max(b => b.Start)) + 1);
        var clones = callee.Blocks.ToDictionary(b => b, b => new Block(label++) { End = label });
        var labels = clones.ToDictionary(p => p.Key.Start, p => p.Value.Start);
        var returns = new Dictionary<Block, Variable>();
        foreach (var source in callee.Blocks)
        {
            var clone = clones[source];
            foreach (var original in source.Statements.Where(s => s is not Store store || !saved.Contains(store)))
            {
                var mapped = ExprMap.MapOperands(original, Map);
                if (mapped is Return { Value: { } value } && output is not null)
                {
                    var returned = new Variable(output.Storage, versions.GetValueOrDefault(output.Storage) + 1);
                    versions[output.Storage] = returned.Version;
                    returns[clone] = returned;
                    clone.Statements.Add(new Define(mapped.Address, returned, value));
                }
                clone.Statements.Add(mapped switch
                {
                    Define d => d with { Target = renamed[d.Target] },
                    Phi p => p with { Target = renamed[p.Target], Sources = p.Sources.Select(v => renamed[v]).ToArray() },
                    Call c => c with { Defines = c.Defines.Select(v => v is null ? null! : renamed[v]).ToArray(), NativeExceptionSite = call.NativeExceptionSite ?? call.Address },
                    Branch b => b with { Target = labels[b.Target], Fallthrough = labels[b.Fallthrough] },
                    Jump j => j with { Target = labels[j.Target] },
                    Return r => new Jump(r.Address, continuation.Start),
                    _ => mapped with { },
                });
            }
            clone.Predecessors.AddRange(source.Predecessors.Select(p => clones[p]));
            clone.Successors.AddRange(source.Successors.Select(p => clones[p]));
        }
        var handler = block.Handler;
        if (split)
        {
            foreach (var successor in block.Successors)
            {
                var predecessor = successor.Predecessors.IndexOf(block);
                successor.Predecessors[predecessor] = continuation;
                continuation.Successors.Add(successor);
            }
            block.Successors.Clear();
            block.Statements.RemoveRange(index + 1, block.Statements.Count - index - 1);
            caller.Blocks.Add(continuation);
        }
        var normalValues = split ? [] : EdgeValues(block, continuation);
        var exceptionalValues = handler is null ? [] : EdgeValues(block, handler);
        while (block.Successors.Count > 0) MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
        block.Statements.RemoveAt(block.Statements.Count - 1);
        block.Statements.AddRange(bindings);
        block.Statements.Add(new Jump(call.Address, clones[callee.EntryBlock].Start));
        MachineFunction.AddEdge(block, clones[callee.EntryBlock]);
        foreach (var source in callee.Blocks)
        {
            var clone = clones[source];
            if (source.Statements.LastOrDefault() is Return) Connect(clone, continuation, normalValues);
            if (handler is not null && clone.Statements.Any(s => s is Call))
            {
                Connect(clone, handler, exceptionalValues);
                clone.Handler = handler;
            }
        }
        caller.Blocks.AddRange(clones.Values);
        if (output is not null)
            continuation.Statements.Insert(0, new Phi(continuation.Start, output, continuation.Predecessors.Select(b => returns[b]).ToArray()));
        caller.Renumber();
        return true;
    }

    private static Variable[] EdgeValues(Block from, Block to)
    {
        var index = MachineFunction.PredecessorIndex(from, from.Successors.LastIndexOf(to));
        return to.Statements.OfType<Phi>().Select(p => p.Sources[index]).ToArray();
    }

    private static void Connect(Block from, Block to, Variable[] values)
    {
        MachineFunction.AddEdge(from, to);
        var index = 0;
        for (var i = 0; i < to.Statements.Count; i++)
            if (to.Statements[i] is Phi phi) to.Statements[i] = phi with { Sources = [.. phi.Sources, values[index++]] };
    }

    private static IEnumerable<Variable> Defined(Stmt statement) => statement switch
    {
        Define d => [d.Target],
        Phi p => [p.Target],
        Call c => c.Defines.Where(v => v is not null),
        _ => [],
    };
}
