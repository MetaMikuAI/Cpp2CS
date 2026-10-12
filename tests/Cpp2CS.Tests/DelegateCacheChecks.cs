using System.Text.Json;
using Cpp2CS.Native;

public static class DelegateCacheChecks
{
    public static void Run(Action<bool, string> check)
    {
        var type = new MetadataExpression(new(1, "ScriptMetadata", "Example_TypeInfo", "Example_c*", 0), false);
        var fields = new MemberExpression(type, new("static_fields", "Example_StaticFields*", 184, 8, "Example_c"), "static_fields", null);
        var slot = new MemberExpression(fields, new("cache", "Delegate_o*", 8, 8, "Example_StaticFields"), "cache", null);
        var target = new MemberExpression(fields, new("instance", "Example_o*", 0, 8, "Example_StaticFields"), "instance", null);
        var info = new MetadataExpression(new(2, "ScriptMetadataMethod", "Method$Example.Callback()", "", 0), false);
        var captured = new CapturedExpression("cached", slot);
        var allocated = new NameExpression("created");
        var method = new NativeMethod(0x100, "Example$$Use", "void", [], "");
        var graph = new NativeGraph([new(0x100, "ret", "", [], false, false, "")], _ => false);
        var source = new LiftResult(method, [], new()
        {
            [0x100] = new(0x100, [new DeclareStatement(0x100, "joined", "Delegate_o*"), new AssignStatement(0x104, "cached", slot, "Delegate_o*"),
                new SetLocalStatement(0x100, "joined", captured)], new BinaryExpression("is not", captured, new NameExpression("null")), [0x300, 0x200]),
            [0x200] = new(0x200, [new AssignStatement(0x200, "target", target, "Example_o*"),
                new CallStatement(0x204, "Runtime.Allocate<System.Action>", [], "created", "Delegate_o*", false, null),
                new CallStatement(0x208, ".ctor", [new CapturedExpression("target", target), info], null, "void", true, allocated) { DeclaringType = "System.Action" },
                new StoreStatement(0x20c, slot, allocated), new CallStatement(0x210, "Runtime.GCWriteBarrier", [new AddressOfExpression(slot)], null, "void", false, null),
                new SetLocalStatement(0x200, "joined", allocated)], null, [0x300]),
            [0x300] = new(0x300, [new ReturnStatement(0x300, new NameExpression("joined"))], null, [])
        }, [], [], graph);
        int Count(LiftResult value, Func<string, bool>? predicate = null) => DelegateCaches.Normalize(value, predicate ?? (t => t == "System.Action"))
            .Blocks.Values.SelectMany(b => b.Statements).OfType<DelegateCacheStatement>().Count();
        LiftResult Change(Func<List<Statement>, List<Statement>> change) => source with { Blocks = source.Blocks.ToDictionary(p => p.Key,
            p => p.Value with { Statements = p.Key == 0x200 ? change([.. p.Value.Statements]) : [.. p.Value.Statements] }) };
        check(Count(source) == 1, "缓存菱形恢复为单次读取与条件创建");
        check(source.Blocks.Count == 3 && source.Blocks[0x200].Statements.Count == 6, "缓存归约不修改原始 IR");
        check(Count(source, _ => false) == 0, "非委托类型不能折叠");
        check(Count(Change(s => { s.Insert(1, new CallStatement(0x202, "UserEffect", [], null, "void", false, null)); return s; })) == 0, "额外调用副作用阻止缓存折叠");
        check(Count(Change(s => { s[3] = ((StoreStatement)s[3]) with { Target = target }; return s; })) == 0, "不同写入槽位不能折叠");
        check(Count(Change(s => { s[4] = ((CallStatement)s[4]) with { Arguments = [new AddressOfExpression(target)] }; return s; })) == 0, "写屏障必须对应缓存槽");
        check(Count(Change(s => { s[5] = ((SetLocalStatement)s[5]) with { Value = new NameExpression("wrong") }; return s; })) == 0, "合流必须返回同一个新委托");
        check(Count(Change(s => { s[2] = ((CallStatement)s[2]) with { DeclaringType = "Other" }; return s; })) == 0, "构造方法必须属于分配的委托类型");
        check(Count(Change(s => { s[1] = ((CallStatement)s[1]) with { ReturnType = "Other_o*" }; return s; })) == 0, "缓存字段与分配类型必须匹配");
        check(Count(Change(s => { (s[0], s[1]) = (s[1], s[0]); return s; })) == 0, "分配后的目标读取不能提前到分配前");
        var escaped = source with { Blocks = new(source.Blocks) };
        escaped.Blocks[0x300] = source.Blocks[0x300] with { Statements = [new ReturnStatement(0x300, captured)] };
        check(Count(escaped) == 0, "缓存读取的外部使用必须保留");
        var flag = new MemberExpression(type, new("cctor_finished", "uint32_t", 224, 4, "Example_c"), "cctor_finished", null);
        var flagValue = new CapturedExpression("flag", flag);
        var initCall = new CallStatement(0x200, "Runtime.InitializeClass", [type], null, "void", false, null);
        var initGraph = source with { Blocks = new()
        {
            [0x100] = new(0x100, [new AssignStatement(0x100, "flag", flag, "uint32_t")], new BinaryExpression("!=", flagValue, new ConstantExpression(0)), [0x300, 0x200]),
            [0x200] = new(0x200, [initCall], null, [0x300]),
            [0x300] = new(0x300, [new ReturnStatement(0x300, null)], null, [])
        } };
        check(ViewNormalizer.Normalize(initGraph).Proofs.Any(p => p.Rule == "ViewClassInitialization"), "同类型初始化守卫恢复为语义操作");
        var escapedFlag = initGraph with { Blocks = new(initGraph.Blocks) };
        escapedFlag.Blocks[0x300] = new(0x300, [new ReturnStatement(0x300, flagValue)], null, []);
        check(!ViewNormalizer.Normalize(escapedFlag).Proofs.Any(p => p.Rule == "ViewClassInitialization"), "外部使用的初始化标志不能删除");
        var otherInit = initGraph with { Blocks = new(initGraph.Blocks) };
        otherInit.Blocks[0x200] = new(0x200, [initCall with { Arguments = [type with { Reference = type.Reference with { Slot = 99 } }] }], null, [0x300]);
        check(!ViewNormalizer.Normalize(otherInit).Proofs.Any(p => p.Rule == "ViewClassInitialization"), "初始化其他类型不视为当前类型守卫");
        // 独立检查 C# ??= 的热缓存与冷缓存求值次数。
        foreach (var cachedValue in new object?[] { null, new object() })
        {
            object? original = cachedValue, folded = cachedValue; var originalCalls = 0; var foldedCalls = 0; var created = new object();
            var originalResult = original;
            if (originalResult is null) { originalCalls++; originalResult = created; original = originalResult; }
            object Create() { foldedCalls++; return created; }
            var foldedResult = folded ??= Create();
            check(ReferenceEquals(originalResult, foldedResult) && ReferenceEquals(original, folded) && originalCalls == foldedCalls,
                cachedValue is null ? "冷缓存只创建一次且返回写入值" : "热缓存不求值创建分支");
        }
    }

    public static void Native(Action<bool, string> check, string config)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!);
        foreach (var name in new[] { "ApplySerializeFieldSettings", "GetUnCheckedIds", "IsAllCheck" })
        {
            var native = session.Symbols.NamedMethods["Sekai.Mysekai.BGMVocalCharacterContent$$" + name].Single();
            var result = session.Recover(native.Address);
            var view = session.View(result);
            var caches = view.Blocks.Values.SelectMany(b => b.Statements).OfType<DelegateCacheStatement>().ToArray();
            check(result.Problems.Count == 0 && caches.Length > 0, $"0x{native.Address:x} {name}: 真实委托缓存恢复 ({caches.Length})");
            if (name != "ApplySerializeFieldSettings") continue;
            check(caches.Length == 2 && caches.Select(c => c.Cache.Field.Offset).SequenceEqual(new[] { 8, 16 }), "两个缓存字段保持独立");
            var calls = view.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>().ToArray();
            check(calls.Count(c => c.Name == "Runtime.EnsureClassInitialized") == 1, "同类型重复初始化只在支配证明后消除");
            check(calls.Any(c => c.Name == "System.Linq.Enumerable.SelectMany<RectTransform, UIPartsCharacterIconAndCheckBox>") &&
                calls.Any(c => c.Name == "Sekai.Extensions.CollectionExtensions.ForEach<UIPartsCharacterIconAndCheckBox>"), "共享泛型调用保留实际 MethodInfo 类型实参");
            foreach (var cache in caches)
            {
                var reference = cache.Method.Reference.Name[7..^2];
                var separator = ManagedNames.LastTopLevelDot(reference);
                var lambda = session.Symbols.NamedMethods[reference[..separator] + "$$" + reference[(separator + 1)..]].Single();
                var body = session.Recover(lambda.Address);
                check(body.Problems.Count == 0, $"0x{lambda.Address:x}: lambda 真实方法体恢复");
                var text = new SemanticWriter(session.Symbols).Structured(session.View(body));
                check(!text.Contains("this."), "两个 lambda 均未访问捕获环境字段");
                if (lambda.Address == 0x59219a0) check(text.Contains("GetComponentsInChildren<UIPartsCharacterIconAndCheckBox>"), "实例泛型调用使用 MethodInfo 类型实参");
            }
        }
    }
}
