using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class StackCallsRules
{
    /// <summary>隐藏栈参数需要同时证明调用时 SP、精确 ABI 槽位和未被覆盖的到达写入；附近同名符号不够。</summary>
    [Analysis("栈上调用", 20)]
    internal static void PrepareStackCalls(this RecoveryScope ctx)
    {
        var statements = ctx.blocks.SelectMany(b => b.Statements).ToArray();
        var symbols = statements.OfType<Store>().Where(s => s.Value.Width == 64).Select(s => (Store: s, Symbol: ctx.StackSymbol(s.Value))).Where(p => p.Symbol is not null).ToArray();
        var definitions = ctx.values.Concat(ctx.function.Dead.Select(d => new KeyValuePair<Variable, Expr>(d.Define.Target, d.Define.Value))).GroupBy(p => p.Key).ToDictionary(g => g.Key, g => g.First().Value);
        long? Offset(Expr expression, HashSet<Variable>? active = null)
        {
            active ??= [];
            return expression switch
            {
                FrameAddress f => f.Offset,
                Binary { Op: BinOp.Add, Right: Const c } b when Offset(b.Left, active) is { } offset => offset + c.Signed,
                Binary { Op: BinOp.Sub, Right: Const c } b when Offset(b.Left, active) is { } offset => offset - c.Signed,
                Use u when active.Add(u.Variable) && definitions.TryGetValue(u.Variable, out var value) => Offset(value, active),
                _ => null,
            };
        }

        var sp = ctx.owner.lifter.Machine.Convention.StackPointer;
        var writes = ctx.blocks.ToDictionary(b => b, b => b.Statements.OfType<Define>().Concat(ctx.function.Dead.Where(d => d.Block == b).Select(d => d.Define)).Where(d => d.Target.Storage == sp).DistinctBy(d => d.Target).OrderBy(d => d.Address).ToArray());
        var outputs = ctx.blocks.ToDictionary(b => b, _ => new HashSet<long?>());
        HashSet<long?> Input(Block block)
        {
            var input = block == ctx.function.EntryBlock ? new HashSet<long?>
            {
                0
            }

            : [];
            foreach (var parent in block.Predecessors.Where(outputs.ContainsKey))
                input.UnionWith(outputs[parent]);
            return input;
        }

        bool changed;
        do
        {
            changed = false;
            foreach (var block in ctx.blocks)
            {
                var state = writes[block].LastOrDefault() is { } last ? new HashSet<long?>
                {
                    Offset(last.Value)
                }

                : Input(block);
                if (!outputs[block].SetEquals(state))
                {
                    outputs[block] = state;
                    changed = true;
                }
            }
        }
        while (changed);
        foreach (var block in ctx.blocks)
            foreach (var call in block.Statements.OfType<Call>())
            {
                if (call.Op is not null || call.Target is not Const target)
                    continue;
                var entries = ctx.facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().Select(m => m.Method).Distinct().ToHashSet();
                if (entries.Count == 0)
                    continue;
                var state = writes[block].LastOrDefault(d => d.Address < call.Address) is { } last ? new HashSet<long?>
                {
                    Offset(last.Value)
                }

                : Input(block);
                if (state.Count != 1 || state.Single() is not { } callSp)
                    continue;
                var matches = new List<(MethodRef Method, Store Store)>();
                foreach (var pair in symbols.Where(p => entries.Contains(p.Symbol!.Method)))
                {
                    var candidate = pair.Symbol!;
                    // 开放参数可以保留；已绑定的共享类型和精确 ABI 决定寄存器与隐藏槽位。
                    if (ctx.owner.abi.Classify(candidate, out _) is not { } signature || signature.MethodInfo is not null)
                        continue;
                    var layout = ctx.owner.abi.StackArguments(signature);
                    if (layout.MethodInfoOffset is not { } hidden || ctx.FrameOffset(pair.Store.Target) != callSp + hidden)
                        continue;
                    if (!signature.Reads.ToHashSet().SetEquals(call.Sources))
                        continue;
                    if (!ReferenceEquals(ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + hidden, []), pair.Store))
                        continue;
                    matches.Add((candidate, pair.Store));
                }

                // 非泛型等调用可传空 MethodInfo；身份由调用目标解析，槽位仍按精确签名与 SP 核对。
                if (ctx.Resolve(call) is { } direct && ctx.owner.abi.Classify(direct, out _) is { MethodInfo: null } directSignature && directSignature.Reads.ToHashSet().SetEquals(call.Sources) && ctx.owner.abi.StackArguments(directSignature).MethodInfoOffset is { } directHidden && ctx.ReachingStackStore(block, block.Statements.IndexOf(call), callSp + directHidden, []) is { Value: Const { Value: 0, Width: 64 } } zero)
                    matches.Add((direct, zero));
                var unique = matches.Distinct().ToArray();
                if (unique is not [var match])
                    continue;
                ctx.State.Calls.callBindings.Commit(call, match.Method);
                ctx.State.Lowering.dropped.Add(match.Store);
                ctx.owner.stackCalls.Add(new(ctx.entry, call.Address, match.Store.Address, callSp, ctx.FrameOffset(match.Store.Target)!.Value, match.Method));
            }
    }

    internal static MethodRef? StackSymbol(this RecoveryScope ctx, Expr expression)
    {
        var active = new HashSet<Variable>();
        while (expression is Use u && active.Add(u.Variable) && ctx.values.TryGetValue(u.Variable, out var value))
            expression = value;
        return expression is Symbol { Kind: SymbolKind.Method, Value: MethodRef method } ? method : null;
    }

    internal static Store? ReachingStackStore(this RecoveryScope ctx, Block block, int before, long offset, HashSet<Block> active, int width = 64, bool allowWider = false)
    {
        if (!active.Add(block))
            return null;
        for (var i = before - 1; i >= 0; i--)
        {
            var statement = block.Statements[i];
            if (statement is Call { Op.Kind: not OpKind.WriteBarrier } or Call { Op: null })
                return null;
            if (statement is not Store store)
                continue;
            if (ctx.FrameOffset(store.Target) is not { } at)
                return null;
            if (at < offset + width / 8 && offset < at + store.Value.Width / 8)
                return at == offset && (store.Value.Width == width || allowWider && store.Value.Width > width && store.Value.Width <= 64) ? store : null;
        }

        var parents = block.Predecessors.Where(p => ctx.blocks.Contains(p)).ToArray();
        if (parents.Length == 0)
            return null;
        var sources = parents.Select(p => ctx.ReachingStackStore(p, p.Statements.Count, offset, new(active), width, allowWider)).ToArray();
        return sources[0] is { } source && sources.All(s => ReferenceEquals(s, source)) ? source : null;
    }
}
