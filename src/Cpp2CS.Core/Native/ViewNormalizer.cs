namespace Cpp2CS.Native;

// 仅在明确的控制流与相邻使用条件下简化视图；原始 IR 保持不变。
public static class ViewNormalizer
{
    public static LiftResult Normalize(LiftResult source)
    {
        var blocks = source.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = [.. p.Value.Statements] });
        var result = source with { Blocks = blocks, Proofs = [.. source.Proofs] };
        if (source.Problems.Count > 0) return result;
        foreach (var block in blocks.Values.ToArray())
        {
            if (block.Condition is not BinaryExpression { Operator: "==" or "!=", Left: CapturedExpression flag, Right: ConstantExpression { Value: 0 } } condition ||
                flag.Value is not AddressExpression address || block.Successors.Length != 2) continue;
            var loads = block.Statements.OfType<AssignStatement>().Where(a => a.Name == flag.Name && a.Value == address).ToArray();
            if (loads.Length != 1 || block.Statements.SkipWhile(s => s != loads[0]).Skip(1).Any(s => s is not AssignStatement)) continue;
            var initIndex = condition.Operator == "==" ? 0 : 1;
            var join = block.Successors[1 - initIndex];
            var init = blocks[block.Successors[initIndex]];
            if (loads.Length != 1 || blocks.Values.Sum(b => b.Statements.Sum(s => Expressions(s).Sum(e => Count(e, flag.Name))) + (b.Condition is null ? 0 : Count(b.Condition, flag.Name))) != 1 ||
                blocks.Values.Count(b => b.Successors.Contains(init.Address)) != 1 || !init.Successors.SequenceEqual(new[] { join }) ||
                init.Statements.LastOrDefault() is not StoreStatement { Target: AddressExpression target, Value: ConstantExpression { Value: 1 } } || target != address ||
                init.Statements.Count < 2 || !init.Statements.SkipLast(1).All(s => s is CallStatement { Name: "Runtime.InitializeMetadata", Arguments: [MetadataExpression { IsSlot: true }] })) continue;
            var references = init.Statements.SkipLast(1).Cast<CallStatement>().Select(c => ((MetadataExpression)c.Arguments[0]).Reference).ToArray();
            blocks[block.Address] = block with { Statements = [.. block.Statements.Where(s => s != loads[0]), new EnsureMetadataStatement(block.Address, address.Address, references)],
                Condition = null, Successors = [join] };
            result.Proofs.Add(new(block.Address, "ViewMetadataByteGuard", "single-use byte guard; closed metadata-only initialization; same flag store; intervening business reads stay in place"));
        }
        foreach (var block in blocks.Values.ToArray())
        {
            if (block.Condition is BinaryExpression { Operator: "!=", Left: BinaryExpression { Operator: "&", Left: CapturedExpression flag, Right: ConstantExpression { Value: 1 } }, Right: ConstantExpression { Value: 0 } } &&
                block.Statements.LastOrDefault() is AssignStatement { Value: AddressExpression address } &&
                block.Statements.SkipLast(1).All(s => s is DeclareStatement) && flag.Value == address && block.Successors.Length == 2)
            {
                var init = blocks[block.Successors[1]];
                var predecessors = blocks.Values.Count(b => b.Successors.Contains(init.Address));
                if (predecessors == 1 && init.Successors.SequenceEqual(new[] { block.Successors[0] }) &&
                    init.Statements.LastOrDefault() is StoreStatement { Target: AddressExpression target, Value: ConstantExpression { Value: 1 } } && target.Address == address.Address &&
                    init.Statements.Count > 1 && init.Statements.SkipLast(1).All(s => s is CallStatement { Name: "Runtime.InitializeMetadata", Arguments: [MetadataExpression { IsSlot: true }] }))
                {
                    var references = init.Statements.SkipLast(1).Cast<CallStatement>().Select(c => ((MetadataExpression)c.Arguments[0]).Reference).ToArray();
                    blocks[block.Address] = block with { Statements = [.. block.Statements.SkipLast(1), new EnsureMetadataStatement(block.Address, address.Address, references)], Condition = null, Successors = [block.Successors[0]] };
                    result.Proofs.Add(new(block.Address, "ViewMetadataRegion", "closed flag-bit guard, only metadata resolution calls, final same-flag store; intrinsic retains synchronization and exceptions"));
                }
            }
        }
        foreach (var block in blocks.Values.ToArray())
        {
            if (block.Condition is not BinaryExpression { Operator: "!=", Left: CapturedExpression captured, Right: ConstantExpression { Value: 0 } } ||
                captured.Value is not MemberExpression { Field.Name: "cctor_finished", Receiver: MetadataExpression { IsSlot: false, Reference.Kind: "ScriptMetadata" } type } ||
                block.Statements.LastOrDefault() is not AssignStatement load || load.Name != captured.Name || load.Value != captured.Value ||
                block.Successors.Length != 2) continue;
            if (blocks.Values.Sum(b => b.Statements.Sum(s => Expressions(s).Sum(e => Count(e, captured.Name))) +
                (b.Condition is null ? 0 : Count(b.Condition, captured.Name))) != 1) continue;
            var init = blocks[block.Successors[1]];
            if (blocks.Values.Count(b => b.Successors.Contains(init.Address)) != 1 ||
                !init.Successors.SequenceEqual(new[] { block.Successors[0] }) ||
                init.Statements is not [CallStatement { Name: "Runtime.InitializeClass", Arguments: [MetadataExpression argument] }] || argument != type) continue;
            blocks[block.Address] = block with { Statements = [.. block.Statements.SkipLast(1),
                new CallStatement(load.Address, "Runtime.EnsureClassInitialized", [type], null, "void", false, null)], Condition = null, Successors = [block.Successors[0]] };
            result.Proofs.Add(new(load.Address, "ViewClassInitialization", "same type cctor_finished guard and sole initialization call; intrinsic retains guard, failure and synchronization"));
        }
        foreach (var block in blocks.Values.ToArray())
        {
            if (block.Condition is not BinaryExpression { Operator: "is", Right: NameExpression { Name: "null" } } guard || block.Successors.Length != 2) continue;
            var yes = blocks[block.Successors[0]]; var no = blocks[block.Successors[1]];
            if (yes.Statements is [ThrowStatement { Type: "System.NullReferenceException" }] &&
                no.Statements.FirstOrDefault() is AssignStatement { Value: MemberExpression member } && member.Receiver == guard.Left)
            {
                blocks[block.Address] = block with { Condition = null, Successors = [no.Address] };
                result.Proofs.Add(new(block.Address, "ViewImplicitNullCheck", "immediately following field access performs the same null check before any other effect"));
            }
            else if (yes.Statements is [ReturnStatement { Value: null }] &&
                no.Statements is [CallStatement { IsInstance: true, Name: "Invoke", Result: null } call, ReturnStatement { Value: null }] && call.Receiver == guard.Left)
            {
                blocks[block.Address] = block with { Statements = [.. block.Statements, new ConditionalInvokeStatement(call.Address, call.Receiver!, call.Arguments), new ReturnStatement(call.Address, null)], Condition = null, Successors = [] };
                result.Proofs.Add(new(block.Address, "ViewConditionalInvoke", "single captured delegate; null path returns; nonnull path only invokes then returns"));
            }
        }
        Prune();
        var allTypes = blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>()
            .Where(c => c.Name == "Runtime.EnsureClassInitialized" && c.Arguments is [MetadataExpression])
            .Select(c => (MetadataExpression)c.Arguments[0]).ToHashSet();
        var initialized = blocks.Keys.ToDictionary(k => k, _ => new HashSet<MetadataExpression>(allTypes));
        HashSet<MetadataExpression> EntryTypes(ulong address)
        {
            var predecessors = blocks.Values.Where(b => b.Successors.Contains(address)).Select(b => b.Address).ToArray();
            var known = address == source.Method.Address || predecessors.Length == 0 ? [] : new HashSet<MetadataExpression>(initialized[predecessors[0]]);
            foreach (var predecessor in predecessors.Skip(1)) known.IntersectWith(initialized[predecessor]);
            return known;
        }
        var initializationChanged = true;
        while (initializationChanged)
        {
            initializationChanged = false;
            foreach (var block in blocks.Values)
            {
                var known = EntryTypes(block.Address);
                known.UnionWith(block.Statements.OfType<CallStatement>().Where(c => c.Name == "Runtime.EnsureClassInitialized" && c.Arguments is [MetadataExpression]).Select(c => (MetadataExpression)c.Arguments[0]));
                if (!known.SetEquals(initialized[block.Address])) { initialized[block.Address] = known; initializationChanged = true; }
            }
        }
        foreach (var address in blocks.Keys)
        {
            var block = blocks[address];
            var known = EntryTypes(address);
            block.Statements.RemoveAll(s =>
            {
                if (s is not CallStatement { Name: "Runtime.EnsureClassInitialized", Arguments: [MetadataExpression type] }) return false;
                if (known.Add(type)) return false;
                result.Proofs.Add(new(s.Address, "ViewDominatingClassInitialization", "same type initialized on every incoming path; successful class initialization persists"));
                return true;
            });
            initialized[address] = known;
        }
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var block in blocks.Values.ToArray())
            {
                if (block.Successors.Length != 1 || block.Successors[0] == source.Method.Address || block.Successors[0] == block.Address) continue;
                var next = blocks[block.Successors[0]];
                if (source.Finally is { } cleanup && (next.Address == cleanup.Header || next.Address == cleanup.Cleanup || next.Address == cleanup.Continuation || block.Address == cleanup.Cleanup)) continue;
                if (blocks.Values.Count(b => b.Successors.Contains(next.Address)) != 1) continue;
                blocks[block.Address] = block with { Statements = [.. block.Statements, .. next.Statements], Condition = next.Condition, Successors = next.Successors };
                blocks.Remove(next.Address); changed = true; break;
            }
        }
        foreach (var block in blocks.Values)
        {
            for (var i = 0; i < block.Statements.Count;)
            {
                if (block.Statements[i] is not AssignStatement assignment) { i++; continue; }
                var uses = blocks.Values.Sum(b => b.Statements.Sum(s => Expressions(s).Sum(e => Count(e, assignment.Name))) + (b.Condition is null ? 0 : Count(b.Condition, assignment.Name)));
                if (uses == 0 && assignment.Value is OperationExpression { Operation: ValueOperation.Select } select && Pure(select))
                {
                    block.Statements.RemoveAt(i);
                    result.Proofs.Add(new(assignment.Address, "ViewDeadPureValue", "unused select over already evaluated values; no memory access, call or trapping operation removed"));
                    i = 0;
                    continue;
                }
                if (uses != 1) { i++; continue; }
                if (i + 1 < block.Statements.Count && Expressions(block.Statements[i + 1]).Any(e => ConditionalUse(e, assignment.Name))) { i++; continue; }
                if (i + 1 < block.Statements.Count && Expressions(block.Statements[i + 1]).Any(e => Count(e, assignment.Name) == 1))
                    block.Statements[i + 1] = Replace(block.Statements[i + 1], assignment.Name, assignment.Value);
                else if (i + 1 == block.Statements.Count && blocks[block.Address].Condition is { } condition && Count(condition, assignment.Name) == 1)
                    blocks[block.Address] = blocks[block.Address] with { Condition = Replace(condition, assignment.Name, assignment.Value) };
                else { i++; continue; }
                block.Statements.RemoveAt(i);
                result.Proofs.Add(new(assignment.Address, "ViewAdjacentInline", "one use in immediately adjacent statement/condition; no intervening read, write or call"));
                i = 0;
            }
        }
        return result;
        void Prune()
        {
            var seen = new HashSet<ulong>(); var pending = new Queue<ulong>(); pending.Enqueue(source.Method.Address);
            while (pending.TryDequeue(out var address)) { if (!seen.Add(address)) continue; foreach (var successor in blocks[address].Successors) pending.Enqueue(successor); }
            foreach (var key in blocks.Keys.Where(k => !seen.Contains(k)).ToArray()) blocks.Remove(key);
        }
    }
    internal static IEnumerable<Expression> Expressions(Statement s) => s switch
    {
        AssignStatement a => [a.Value], CallStatement c => c.Receiver is null ? c.Arguments : [c.Receiver, .. c.Arguments],
        ConditionalInvokeStatement c => [c.Receiver, .. c.Arguments], StoreStatement w => [w.Target, w.Value],
        DelegateCacheStatement c => [c.Cache, c.Target, c.Method],
        ReturnStatement { Value: { } value } => [value], SetLocalStatement s1 => [s1.Value], _ => []
    };
    private static bool Pure(Expression expression) => expression switch
    {
        NameExpression or ConstantExpression or CapturedExpression => true,
        BinaryExpression b when b.Operator is "==" or "!=" or "<" or "<=" or ">" or ">=" or "&" or "|" => Pure(b.Left) && Pure(b.Right),
        OperationExpression { Operation: ValueOperation.Select or ValueOperation.IntegerCast or ValueOperation.Unsigned } o => o.Arguments.All(Pure),
        _ => false
    };
    internal static int Count(Expression e, string name) => e switch
    {
        LambdaExpression l => l.Parameters.Contains(name) ? 0 : Count(l.Body, name),
        LambdaBlockExpression l => l.Body.Blocks.Values.Sum(b => b.Statements.SelectMany(Expressions).Sum(e => Count(e, name)) + (b.Condition is null ? 0 : Count(b.Condition, name))),
        OperationExpression o => o.Arguments.Sum(a => Count(a, name)),
        InvocationExpression c => (c.Receiver is null ? 0 : Count(c.Receiver, name)) + c.Arguments.Sum(a => Count(a, name)),
        CapturedExpression c => c.Name == name ? 1 : 0, NameExpression n => n.Name == name ? 1 : 0,
        SliceExpression s => Count(s.Value, name), ComposeExpression c => c.Parts.Sum(p => Count(p, name)),
        AggregateExpression a => Count(a.Bits, name),
        MemberExpression m => Count(m.Receiver, name), AddressOfExpression a => Count(a.Target, name), BinaryExpression b => Count(b.Left, name) + Count(b.Right, name), _ => 0
    };
    private static bool ConditionalUse(Expression e, string name) => e switch
    {
        LambdaExpression l => Count(l, name) != 0,
        LambdaBlockExpression l => Count(l, name) != 0,
        OperationExpression o => o.Operation == ValueOperation.Select && o.Arguments.Skip(1).Any(a => Count(a, name) > 0) || o.Arguments.Any(a => ConditionalUse(a, name)),
        InvocationExpression c => (c.Receiver is not null && ConditionalUse(c.Receiver, name)) || c.Arguments.Any(a => ConditionalUse(a, name)),
        MemberExpression m => ConditionalUse(m.Receiver, name), AddressOfExpression a => ConditionalUse(a.Target, name),
        BinaryExpression b => ConditionalUse(b.Left, name) || ConditionalUse(b.Right, name),
        SliceExpression s => ConditionalUse(s.Value, name), AggregateExpression a => ConditionalUse(a.Bits, name),
        ComposeExpression c => c.Parts.Any(p => ConditionalUse(p, name)), _ => false
    };
    private static Expression Replace(Expression e, string name, Expression value) => e switch
    {
        OperationExpression o => o with { Arguments = o.Arguments.Select(a => Replace(a, name, value)).ToArray() },
        InvocationExpression c => c with { Receiver = c.Receiver is null ? null : Replace(c.Receiver, name, value), Arguments = c.Arguments.Select(a => Replace(a, name, value)).ToArray() },
        CapturedExpression c when c.Name == name => value,
        NameExpression n when n.Name == name => value,
        MemberExpression m => m with { Receiver = Replace(m.Receiver, name, value) },
        AddressOfExpression a => a with { Target = Replace(a.Target, name, value) },
        SliceExpression s => s with { Value = Replace(s.Value, name, value) },
        ComposeExpression c => c with { Parts = c.Parts.Select(p => Replace(p, name, value)).ToArray() },
        AggregateExpression a => a with { Bits = Replace(a.Bits, name, value) },
        BinaryExpression b => b with { Left = Replace(b.Left, name, value), Right = Replace(b.Right, name, value) }, _ => e
    };
    private static Statement Replace(Statement s, string name, Expression value) => s switch
    {
        AssignStatement a => a with { Value = Replace(a.Value, name, value) },
        CallStatement c => c with { Receiver = c.Receiver is null ? null : Replace(c.Receiver, name, value), Arguments = c.Arguments.Select(e => Replace(e, name, value)).ToArray() },
        ConditionalInvokeStatement c => c with { Receiver = Replace(c.Receiver, name, value), Arguments = c.Arguments.Select(e => Replace(e, name, value)).ToArray() },
        ReturnStatement r => r with { Value = r.Value is null ? null : Replace(r.Value, name, value) },
        StoreStatement w => w with { Target = Replace(w.Target, name, value), Value = Replace(w.Value, name, value) },
        DelegateCacheStatement c => c with { Cache = (MemberExpression)Replace(c.Cache, name, value), Target = Replace(c.Target, name, value) },
        SetLocalStatement local => local with { Value = Replace(local.Value, name, value) }, _ => s
    };
}
