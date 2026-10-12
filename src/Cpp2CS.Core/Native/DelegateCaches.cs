namespace Cpp2CS.Native;

// 只归约闭合的空值缓存菱形；任意额外副作用、外部使用或不匹配的存储均保留原图。
public static class DelegateCaches
{
    public static LiftResult Normalize(LiftResult source, Func<string, bool> isDelegate)
    {
        var result = source with { Blocks = source.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = [.. p.Value.Statements] }), Proofs = [.. source.Proofs] };
        if (source.Problems.Count != 0) return result;
        var blocks = result.Blocks;
        foreach (var guard in blocks.Values.ToArray())
        {
            if (guard.Condition is not BinaryExpression { Operator: "is not", Right: NameExpression { Name: "null" }, Left: CapturedExpression cached } ||
                guard.Successors.Length != 2 || guard.Statements.Count < 2 ||
                guard.Statements[^2] is not AssignStatement load || load.Name != cached.Name || Expand(load.Value) != Expand(cached.Value) ||
                Expand(load.Value) is not MemberExpression cache || !StaticField(cache) ||
                guard.Statements[^1] is not SetLocalStatement initial || initial.Value != cached) continue;
            var create = blocks[guard.Successors[1]];
            if (create.Condition is not null || !create.Successors.SequenceEqual(new[] { guard.Successors[0] }) ||
                blocks.Values.Count(b => b.Successors.Contains(create.Address)) != 1) continue;
            var assignments = create.Statements.OfType<AssignStatement>().ToArray();
            if (assignments.Any(a => !StaticRead(Expand(a.Value)))) continue;
            var effects = create.Statements.Where(s => s is not AssignStatement).ToArray();
            if (effects is not [CallStatement allocation, CallStatement ctor, StoreStatement store, CallStatement barrier, SetLocalStatement final] ||
                allocation is not { Arguments.Length: 0, Result: { } allocated, IsInstance: false } ||
                !allocation.Name.StartsWith("Runtime.Allocate<") || !allocation.Name.EndsWith('>') ||
                ctor is not { IsInstance: true, Name: ".ctor", Result: null, Arguments: [var target, MetadataExpression { IsSlot: false, Reference.Kind: "ScriptMetadataMethod" } method] } ||
                ctor.Receiver != new NameExpression(allocated) ||
                Expand(target) is not MemberExpression singleton || !StaticField(singleton) ||
                Expand(store.Target) != cache || store.Value != new NameExpression(allocated) ||
                barrier is not { Name: "Runtime.GCWriteBarrier", Result: null, Arguments: [AddressOfExpression slot] } || Expand(slot.Target) != cache ||
                final.Name != initial.Name || final.Value != new NameExpression(allocated)) continue;
            var type = allocation.Name["Runtime.Allocate<".Length..^1];
            if (singleton.Receiver != cache.Receiver || assignments.Any(a => Expand(a.Value) != singleton && Expand(a.Value) != cache.Receiver) ||
                allocation.ReturnType != cache.Field.Type || target is not CapturedExpression targetRead ||
                assignments.Count(a => Expand(a.Value) == singleton) != 1 ||
                !create.Statements.TakeWhile(s => s != allocation).OfType<AssignStatement>().Any(a => a.Name == targetRead.Name && Expand(a.Value) == singleton)) continue;
            if (!isDelegate(type) || ctor.DeclaringType is null ||
                ManagedNames.SplitGeneric(ctor.DeclaringType).Name != ManagedNames.SplitGeneric(type).Name ||
                ManagedNames.SplitGeneric(ctor.DeclaringType).Arguments.Length != ManagedNames.SplitGeneric(type).Arguments.Length) continue;
            var locals = assignments.Select(a => a.Name).Append(allocated).Append(cached.Name).ToHashSet();
            var outside = blocks.Values.Where(b => b.Address != create.Address).SelectMany(b =>
                b.Statements.Where(s => b.Address != guard.Address || s != load && s != initial).SelectMany(ViewNormalizer.Expressions)
                    .Concat(b.Address != guard.Address && b.Condition is { } c ? [c] : []));
            if (outside.Any(e => locals.Any(n => ViewNormalizer.Count(e, n) != 0))) continue;
            if (blocks.Values.SelectMany(b => b.Statements).OfType<SetLocalStatement>().Count(s => s.Name == initial.Name) != 2 ||
                blocks.Values.SelectMany(b => b.Statements).OfType<DeclareStatement>().Count(s => s.Name == initial.Name) != 1) continue;
            // 目标在分配前读取。缓存写入及写屏障由托管 ??= 保留，右侧仅在缓存为空时求值。
            blocks[guard.Address] = guard with { Statements = [.. guard.Statements.SkipLast(2),
                new DelegateCacheStatement(load.Address, initial.Name, type, cache, singleton, method)], Condition = null, Successors = [guard.Successors[0]] };
            blocks.Remove(create.Address);
            foreach (var block in blocks.Values) block.Statements.RemoveAll(s => s is DeclareStatement d && d.Name == initial.Name);
            result.Proofs.Add(new(load.Address, "ViewDelegateCache", "single-read null diamond; verified delegate allocation/constructor; same static slot store and write barrier; same object on both Phi edges; no escaping temporaries or extra effects; non-atomic cache semantics retained"));
        }
        return result;
    }
    private static bool StaticField(MemberExpression member) => member.Receiver is MemberExpression
        { Field.Name: "static_fields", Receiver: MetadataExpression { IsSlot: false, Reference.Kind: "ScriptMetadata" } };
    private static bool StaticRead(Expression expression) => expression is MemberExpression member &&
        (StaticField(member) || member is { Field.Name: "static_fields", Receiver: MetadataExpression { IsSlot: false, Reference.Kind: "ScriptMetadata" } });
    private static Expression Expand(Expression expression) => expression switch
    {
        CapturedExpression c => Expand(c.Value),
        MemberExpression m => m with { Receiver = Expand(m.Receiver) },
        _ => expression
    };
}
