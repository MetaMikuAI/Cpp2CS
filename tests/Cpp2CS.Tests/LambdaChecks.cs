using System.Text.Json;
using Cpp2CS.Native;

public static class LambdaChecks
{
    public static void Run(Action<bool, string> check)
    {
        var method = new NativeMethod(0x100, "Example.<>c$$<Use>b__0_0", "Object_o*", [new("Example_o*", "__this"), new("Object_o*", "value"), new("MethodInfo*", "method")], "");
        var graph = new NativeGraph([new(0x100, "ret", "", [], false, false, "")], _ => false);
        var call = new CallStatement(0x100, "Convert", [], "result", "Object_o*", true, new NameExpression("value"));
        var source = new LiftResult(method, [], new() { [0x100] = new(0x100, [call, new ReturnStatement(0x104, new NameExpression("result"))], null, []) }, [], [], graph);
        check(LambdaBodies.Expression(source) is { Parameters: ["value"], Body: InvocationExpression { Name: "Convert" } }, "单表达式 lambda 从真实语义调用恢复");
        LiftResult With(params Statement[] statements) => source with { Blocks = new() { [0x100] = new(0x100, statements.ToList(), null, []) } };
        check(LambdaBodies.Expression(With(call with { Receiver = new NameExpression("this") }, new ReturnStatement(0x104, new NameExpression("result")))) is null,
            "读取捕获环境的 lambda 不视为非捕获 lambda");
        check(LambdaBodies.Expression(With(call with { Receiver = new NameExpression("outer") }, new ReturnStatement(0x104, new NameExpression("result")))) is null,
            "自由变量未绑定时保留原方法");
        check(LambdaBodies.Expression(With(call, call with { Result = "second" }, new ReturnStatement(0x108, new NameExpression("second")))) is null,
            "多调用副作用不能丢弃后压成一个表达式");
        check(LambdaBodies.Expression(source with { Problems = ["unknown"] }) is null, "不完整方法体不能内联成 lambda");
        check(LambdaBodies.Expression(With(new ReturnStatement(0x100, new UnknownExpression("missing")))) is null, "未知表达式保持未恢复");
        var fieldRead = new MemberExpression(new NameExpression("value"), new("id", "int32_t", 16, 4, "Object"), "id", "int");
        var capturedField = new CapturedExpression("id", fieldRead);
        var predicate = new BinaryExpression("==", capturedField, new ConstantExpression(3));
        var withDeadSelect = With(new AssignStatement(0x100, "id", fieldRead, "int32_t"),
            new AssignStatement(0x104, "test", new OperationExpression(ValueOperation.Select, "int32_t", [predicate, new ConstantExpression(1), new ConstantExpression(0)]), "int32_t"), new ReturnStatement(0x108, predicate));
        check(LambdaBodies.Expression(withDeadSelect) is { Body: BinaryExpression { Left: MemberExpression } }, "死条件置位消除后恢复字段比较 lambda");
        check(LambdaBodies.Expression(With(new AssignStatement(0x100, "unused", fieldRead, "int32_t"), new ReturnStatement(0x104, new ConstantExpression(1)))) is null,
            "未使用字段读取仍保留空引用副作用");
        var owner = new MetadataExpression(new(1, "ScriptMetadata", "Example_TypeInfo", "Example_c*", 0), false);
        var fields = new MemberExpression(owner, new("static_fields", "Fields*", 184, 8, "Example_c"), "static_fields", null);
        var slot = new MemberExpression(fields, new("cache", "Delegate*", 8, 8, "Fields"), "cache", null);
        var cache = new DelegateCacheStatement(0x100, "cached", "System.Func<Object, Object>", slot, new NameExpression("target"),
            new MetadataExpression(new(2, "ScriptMetadataMethod", "Method$Example.Callback()", "", 0), false));
        var consumer = new CallStatement(0x104, "Consume", [new NameExpression("cached")], null, "void", false, null);
        var cached = With(cache, consumer, new ReturnStatement(0x108, null));
        var lambda = LambdaBodies.Expression(source)!;
        var deferredRead = With(new AssignStatement(0x100, "snapshot", fieldRead, "int32_t"),
            new AssignStatement(0x104, "deferred", new LambdaExpression([], new NameExpression("snapshot"), 0x200), "System.Func<int>"),
            new ReturnStatement(0x108, new NameExpression("deferred")));
        check(ViewNormalizer.Normalize(deferredRead).Blocks[0x100].Statements.First() is AssignStatement { Name: "snapshot" }, "字段读取的求值时点不移入延迟执行的 lambda");
        LambdaProjection Project(LiftResult input) => LambdaProjectionBuilder.Build(input, c => new(c, lambda, source));
        var projected = Project(cached);
        check(projected.Sites.Length == 1 && projected.View.IsSourceProjection &&
            projected.View.Blocks[0x100].Statements[0] is CallStatement { Arguments: [LambdaExpression] }, "单次相邻参数使用投影成 lambda 实参");
        check(cached.Blocks[0x100].Statements[0] is DelegateCacheStatement, "源码投影保留底层缓存节点");
        check(projected.Sites[0].Lambda is { Parameters: ["value2"], Body: InvocationExpression { Receiver: NameExpression { Name: "value2" } } },
            "lambda 参数与外层参数重名时同步重命名绑定");
        check(Project(With(cache, consumer, consumer)).Sites.Length == 0, "多次使用委托身份时保留缓存");
        check(Project(With(cache, new ReturnStatement(0x104, new NameExpression("cached")))).Sites.Length == 0, "返回委托时保留缓存身份");
        check(Project(With(cache, consumer, new ReturnStatement(0x108, slot))).Sites.Length == 0, "缓存字段存在其他读取时拒绝隐藏");
        check(LambdaProjectionBuilder.Build(cached, _ => null).Sites.Length == 0, "身份或签名不匹配时保留底层输出");
    }

    public static void Native(Action<bool, string> check, string config)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!);
        var predicateOwner = session.Recover(0x570e970);
        session.Save(predicateOwner, "artifacts/recovered");
        var predicateView = session.SourceView(session.View(predicateOwner));
        check(predicateView.Sites.Length == 1, "真实体力谓词恢复为 lambda");
        var predicateText = new SemanticWriter(session.Symbols).Structured(predicateView.View);
        check(!predicateText.Contains("static_fields") && !predicateText.Contains("__9") && !predicateText.Contains("MetadataValue"), "已证明的谓词缓存不泄露 static_fields 和编译器名称");
        check(predicateView.Sites.Single().Lambda.Body is BinaryExpression { Right: ConstantExpression { EnumType: "Sekai.MysekaiStaminaType", EnumMember: "boost" } }, "枚举谓词使用真实托管枚举成员");
        Directory.CreateDirectory("artifacts/PredicateFixture");
        File.WriteAllText("artifacts/PredicateFixture/PredicateFixture.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><Nullable>disable</Nullable></PropertyGroup></Project>");
        File.WriteAllText("artifacts/PredicateFixture/Program.cs", $$"""
            using Sekai.ApiData;
            Func<MasterMysekaiStamina, bool> predicate = {{SemanticWriter.Expression(predicateView.Sites.Single().Lambda)}};
            foreach (var value in new[] { -1, 0, 1, 2, 3, int.MaxValue })
                if (predicate(new() { StaminaType = (Sekai.MysekaiStaminaType)value }) != (value == 2)) throw new Exception("predicate mismatch");
            var nullCase = Task.Run(() => predicate(null));
            await nullCase.ContinueWith(_ => { });
            if (nullCase.Exception?.InnerException is not NullReferenceException) throw new Exception("null check lost");
            Console.WriteLine("PASS: generated predicate compiled; 6 enum values and null exception checked");
            namespace Sekai { public enum MysekaiStaminaType { normal = 0, boost = 2 } }
            namespace Sekai.ApiData { public class MasterMysekaiStamina { public Sekai.MysekaiStaminaType StaminaType { get; set; } } }
            """);
        var result = session.Recover(0x591fbe0);
        var lowered = session.View(result);
        var projection = session.SourceView(lowered);
        check(projection.Sites.Length == 2 && projection.Diagnostics.Length == 0, "真实两个 lambda 均通过元数据、签名和方法体验证");
        check(projection.Sites.Select(s => s.Lambda.MethodAddress).SequenceEqual(new ulong[] { 0x59219a0, 0x59219f0 }), "lambda 目标与独立真实入口一致");
        var text = new SemanticWriter(session.Symbols).Structured(projection.View);
        check(text.Contains("buttonRoot => buttonRoot.GetComponentsInChildren<UIPartsCharacterIconAndCheckBox>()") &&
            text.Contains("checkBox => checkBox.ApplySerializeFieldSetting()"), "输出实际 lambda 调用内容");
        check(!text.Contains("__9") && !text.Contains("CreateDelegate") && !text.Contains("MetadataSlot"), "高层视图不泄露已恢复的编译器缓存细节");
        check(lowered.Blocks.Values.SelectMany(b => b.Statements).OfType<DelegateCacheStatement>().Count() == 2, "两个缓存及初始化仍留在底层语义视图");
        var first = lowered.Blocks.Values.SelectMany(b => b.Statements).OfType<DelegateCacheStatement>().First();
        var mutated = lowered with { Blocks = lowered.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = p.Value.Statements.Select(s =>
            s == first ? first with { Method = first.Method with { Reference = first.Method.Reference with { MethodAddress = 0x59219f0 } } } : s).ToList() }) };
        check(session.SourceView(mutated).Sites.All(s => s.Cache.Name != first.Name), "非零 MethodAddress 与名称冲突时拒绝投影");
        var wrongTarget = lowered with { Blocks = lowered.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = p.Value.Statements.Select(s =>
            s == first ? first with { Method = first.Method with { Reference = first.Method.Reference with
            { Name = "Method$Sekai.Mysekai.BGMVocalCharacterContent.<>c.<ApplySerializeFieldSettings>b__14_1()", MethodAddress = 0 } } } : s).ToList() }) };
        check(session.SourceView(wrongTarget).Sites.All(s => s.Cache.Name != first.Name), "不同编号与签名的 lambda 不能互换");
        Directory.CreateDirectory("artifacts/LambdaFixture");
        File.WriteAllText("artifacts/LambdaFixture/LambdaFixture.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><Nullable>enable</Nullable></PropertyGroup></Project>");
        File.WriteAllText("artifacts/LambdaFixture/Program.cs", $$"""
            using UnityEngine;
            using Sekai;
            public class Fixture
            {
                RectTransform[] buttonsRoots = [];
                {{text}}
                public static void Main()
                {
                    var a = new UIPartsCharacterIconAndCheckBox(); var b = new UIPartsCharacterIconAndCheckBox();
                    var fixture = new Fixture { buttonsRoots = [new() { Items = [a, b] }, new() { Items = [a] }] };
                    fixture.ApplySerializeFieldSettings(); fixture.ApplySerializeFieldSettings();
                    if (a.Calls != 4 || b.Calls != 2) throw new InvalidOperationException("lambda 调用次数或参数传递错误");
                    Console.WriteLine("PASS: generated source compiles and invokes both lambdas with expected arguments (stub runtime)");
                }
            }
            namespace UnityEngine
            {
                public class RectTransform
                {
                    public UIPartsCharacterIconAndCheckBox[] Items = [];
                    public T[] GetComponentsInChildren<T>() => Items.Cast<T>().ToArray();
                }
            }
            namespace Sekai
            {
                public class UIPartsCharacterIconAndCheckBox
                {
                    public int Calls;
                    public void ApplySerializeFieldSetting() => Calls++;
                }
            }
            namespace Sekai.Extensions
            {
                public static class CollectionExtensions
                {
                    public static void ForEach<T>(IEnumerable<T> source, Action<T> action)
                    { foreach (var value in source) action(value); }
                }
            }
            """);
    }
}
