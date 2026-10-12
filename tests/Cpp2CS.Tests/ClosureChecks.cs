using System.Text.Json;
using Cpp2CS.Native;

public static class ClosureChecks
{
    public static void Native(Action<bool, string> check, string config)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!;
        using var session = new RecoverySession(inputs);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        var result = session.Recover(0x55d1214);
        session.Save(result, "artifacts/recovered");
        var projection = session.SourceView(session.View(result));
        Console.WriteLine(string.Join("\n", projection.Diagnostics));
        check(projection.Closures.Length == 1, "真实闭包环境恢复为捕获变量");
        var text = new SemanticWriter(session.Symbols).Structured(projection.View);
        check(text.Contains("fixture.name.Contains(capturedFreeWord) || fixture.assetbundleName.Contains(capturedFreeWord)"), "真实谓词保留捕获读取和短路顺序");
        check(text.Contains("UnityEngine.Vector2.zero,"), "静态聚合值由机器 getter 证明为公开属性");
        check(text.Contains(".Count,"), "泛型实例字段恢复为布局匹配的属性");
        check(!text.Contains("static_fields") && !text.Contains("DisplayClass") && !text.Contains("Runtime.") && !text.Contains("MetadataSlot"), "高层回调不泄露已证明的编译器实现");
        var lowered = session.View(result);
        var allocation = lowered.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>().Single(c => c.Name.Contains("Runtime.Allocate<") && c.Name.Contains("DisplayClass"));
        var escaped = SourceTree.Map(lowered, e => e);
        escaped.Blocks[result.Method.Address].Statements.Add(new CallStatement(allocation.Address + 1, "ObserveIdentity", [new NameExpression(allocation.Result!)], null, "void", false, null));
        check(session.SourceView(escaped).Closures.Length == 0, "环境对象传给外部时不消除身份");
        var wrong = SourceTree.Map(lowered, e => e is MetadataExpression { Reference.Kind: "ScriptMetadataMethod" } m && m.Reference.Name.Contains("DisplayClass") ?
            m with { Reference = m.Reference with { MethodAddress = 1 } } : e);
        check(session.SourceView(wrong).Closures.Length == 0, "闭包机器入口与 MethodInfo 冲突时拒绝");
        var capture = projection.Closures.Single();
        check(capture.Bindings.Length == 1 && capture.Lambdas.Length == 1 && capture.Lambdas[0].Lambda.MethodAddress == 0x55d1404, "捕获环境和真实回调绑定完整");
        var mutated = SourceTree.Map(lowered, e => e);
        var write = lowered.Blocks.Values.SelectMany(b => b.Statements).OfType<StoreStatement>().Single(s => s.Target is MemberExpression { Receiver: NameExpression n } && n.Name == allocation.Result);
        var consumerBlock = mutated.Blocks.Values.Single(b => b.Statements.OfType<CallStatement>().Any(c => c.Name.StartsWith("System.Linq.Enumerable.Where")));
        var consumerIndex = consumerBlock.Statements.FindIndex(s => s is CallStatement c && c.Name.StartsWith("System.Linq.Enumerable.Where"));
        consumerBlock.Statements.Insert(consumerIndex, write with { Pc = write.Address + 1, Value = new NameExpression("freeWord") });
        var updated = session.SourceView(mutated);
        check(updated.Closures.Length == 1 && updated.View.Blocks.Values.SelectMany(b => b.Statements).OfType<SetLocalStatement>().Count(s => s.Name == capture.Bindings[0].Name) == 2,
            "委托创建后的捕获赋值仍写同一个变量，不替换为初始值快照");
        var shared = SourceTree.Map(lowered, e => e);
        var creation = shared.Blocks.Values.Single(b => b.Statements.OfType<CallStatement>().Any(c => c.Name.StartsWith("System.Linq.Enumerable.Where")));
        var originalCtor = creation.Statements.OfType<CallStatement>().Single(c => c is { Name: ".ctor", Arguments.Length: 2 });
        var originalName = ((NameExpression)originalCtor.Receiver!).Name;
        var originalAllocation = creation.Statements.OfType<CallStatement>().Single(c => c.Result == originalName);
        var insertion = creation.Statements.IndexOf(originalCtor) + 1;
        creation.Statements.InsertRange(insertion, [originalAllocation with { Pc = originalCtor.Address + 1, Result = "secondDelegate" },
            originalCtor with { Pc = originalCtor.Address + 2, Receiver = new NameExpression("secondDelegate") },
            new CallStatement(originalCtor.Address + 3, "KeepBoth", [new NameExpression(originalName), new NameExpression("secondDelegate")], null, "void", false, null)]);
        var sharedProjection = session.SourceView(shared);
        check(sharedProjection.Closures is [{ Bindings.Length: 1, Lambdas.Length: 2 }], "多个委托共享一个捕获环境，不复制捕获变量");
        var reversed = SourceTree.Map(lowered, e => e is AggregateExpression { Bits: ComposeExpression c } a ?
            a with { Bits = c with { Parts = c.Parts.Reverse().ToArray() } } : e);
        check(!new SemanticWriter(session.Symbols).Structured(session.SourceView(reversed).View).Contains("UnityEngine.Vector2.zero"), "静态聚合分量反序时不视为 getter 返回值");
        check(LambdaBodies.Expression(capture.Lambdas[0].Body) is null, "捕获字段未绑定时不视为普通 lambda");
        File.WriteAllText("artifacts/closure-lambda.txt", SemanticWriter.Expression(capture.Lambdas[0].Lambda));
        Directory.CreateDirectory("artifacts/closure-compiled");
        File.WriteAllText("artifacts/closure-compiled/Callback.cs", "using Sekai.ApiData;\npublic partial class ClosureFixture { public Action<string> CreateCallback() =>\n" + text + ";\n}");
        File.WriteAllText("artifacts/closure-compiled/Predicate.cs", $$"""
            using Sekai.ApiData;
            public partial class ClosureFixture
            {
                public static (Func<MasterMysekaiFixture, bool>, Func<MasterMysekaiFixture, bool>, Action<string>) Capture(string initial)
                {
                    string capturedFreeWord = initial;
                    Func<MasterMysekaiFixture, bool> first = {{SemanticWriter.Expression(capture.Lambdas[0].Lambda)}};
                    Func<MasterMysekaiFixture, bool> second = {{SemanticWriter.Expression(capture.Lambdas[0].Lambda)}};
                    return (first, second, value => capturedFreeWord = value);
                }
            }
            """);
    }
}
