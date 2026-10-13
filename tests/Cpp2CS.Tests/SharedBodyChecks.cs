using System.Text.Json;
using Cpp2CS.Native;

public static class SharedBodyChecks
{
    public static void Run(Action<bool, string> check)
    {
        Instruction[] code = [new(0x100, "ret", "", [], false, false, "")];
        var method = new NativeMethod(0x100, "Example$$Run", "void", [], "");
        EvaluateStatement Call(ulong pc, string name) => new(pc, new InvocationExpression(name, null, [], false));
        var diamond = new LiftResult(method, code, new()
        {
            [0x100] = new(0x100, [], new NameExpression("condition"), [0x104, 0x108]),
            [0x104] = new(0x104, [Call(0x104, "First")], null, [0x10c]),
            [0x108] = new(0x108, [Call(0x108, "Second")], null, [0x10c]),
            [0x10c] = new(0x10c, [Call(0x10c, "Joined"), new ReturnStatement(0x110, null)], null, [])
        }, [], [], new NativeGraph(code, _ => false));
        var writer = new SemanticWriter(null!);
        var normal = writer.Structured(diamond, true);
        var awaited = SourceTree.Map(diamond, value => value is InvocationExpression c ? new AwaitExpression(c) : value);
        var async = writer.Structured(awaited, true);
        check(normal.Split("Joined()").Length == 2 && async.Split("Joined()").Length == 2,
            "普通与 await 分支共用结构化输出，合流业务只输出一次");
        check(normal == async.Replace("await ", ""), "await 包装不改变业务分支结构");
        var inverted = diamond with { Blocks = new()
        {
            [0x100] = new(0x100, [], new BinaryExpression("<", new NameExpression("number"), new ConstantExpression(5)), [0x10c, 0x104]),
            [0x104] = new(0x104, [Call(0x104, "Second")], null, [0x10c]),
            [0x10c] = new(0x10c, [Call(0x10c, "Joined"), new ReturnStatement(0x110, null)], null, [])
        }};
        var invertedText = writer.Structured(inverted, true);
        check(invertedText.Contains("((number < 5) == false)"),
            "结构化分支取反保持布尔类型，且不以相反的浮点关系替代 NaN 语义");
        var selectText = SemanticWriter.Expression(new OperationExpression(ValueOperation.ReferenceSelect, "Example_o*",
            [new NameExpression("condition"), new NameExpression("item"), new NameExpression("null")]));
        Directory.CreateDirectory("artifacts/conditional-fixture");
        File.WriteAllText("artifacts/conditional-fixture/ConditionalFixture.csproj", """
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><Nullable>enable</Nullable></PropertyGroup>
            </Project>
            """);
        var fixture = """
            static class Program
            {
                static int second, joined;
                static void Second() => second++;
                static void Joined() => joined++;
                static void Run(double number) /* BODY */
                static object? Select(bool condition, object item) => /* SELECT */;
                static void Main()
                {
                    foreach (var (number, expected) in new (double, int)[] { (double.NaN, 1), (double.NegativeInfinity, 0), (4, 0), (5, 1), (6, 1), (double.PositiveInfinity, 1) })
                    {
                        second = joined = 0;
                        Run(number);
                        if (second != expected || joined != 1) throw new Exception("branch behavior changed");
                    }
                    var item = new object();
                    if (!ReferenceEquals(Select(true, item), item) || Select(false, item) is not null) throw new Exception("reference identity changed");
                    var snapshot = new SnapshotFixture();
                    snapshot.Run().GetAwaiter().GetResult();
                    if (snapshot.Observed != 7 || snapshot.Field != 9) throw new Exception("field read moved across mutation or await");
                    Console.WriteLine("PASS: generated branches, reference identity and field snapshot across mutation and suspension");
                }
            }
            sealed class SnapshotFixture
            {
                public int Field = 7, Observed;
                void Mutate() => Field = 9;
                async Task Use(int value) { await Task.Yield(); Observed = value; }
                public async Task Run() /* SNAPSHOT */
            }
            """.Replace("/* BODY */", invertedText).Replace("/* SELECT */", selectText);

        var read = new AssignStatement(0x100, "snapshot", new SourceMemberExpression(new NameExpression("this"), "Field", "int"), "int");
        var sequence = diamond with { Blocks = new()
        {
            [0x100] = new(0x100, [read, Call(0x104, "Mutate"),
                new EvaluateStatement(0x108, new AwaitExpression(new InvocationExpression("Use", null, [new NameExpression("snapshot")], false))),
                new ReturnStatement(0x10c, null)], null, [])
        }};
        var normalized = ViewNormalizer.Normalize(sequence);
        var text = writer.Structured(normalized, true);
        File.WriteAllText("artifacts/conditional-fixture/Program.cs", fixture.Replace("/* SNAPSHOT */", text));
        check(normalized.Blocks[0x100].Statements[0] == read && text.IndexOf("this.Field", StringComparison.Ordinal) < text.IndexOf("Mutate()", StringComparison.Ordinal) &&
            text.Contains("await Use(snapshot);"), "字段快照不越过有副作用调用移入 await 参数");
        SemanticValidation.CheckReadSnapshots(sequence, new HashSet<string> { "snapshot" });
        check(sequence.Problems.Count == 0, "字段快照在副作用和 await 之前定义");
        var missingRead = sequence with { Problems = [], Blocks = new() { [0x100] = sequence.Blocks[0x100] with { Statements = [.. sequence.Blocks[0x100].Statements.Skip(1)] } } };
        SemanticValidation.CheckReadSnapshots(missingRead, new HashSet<string> { "snapshot" });
        check(missingRead.Problems.Any(p => p.Contains("字段快照未在所有路径定义")), "协议路径收缩不能丢失仍被使用的字段读取");
        var lateRead = sequence with { Problems = [], Blocks = new() { [0x100] = sequence.Blocks[0x100] with { Statements = [.. sequence.Blocks[0x100].Statements.Skip(1), read] } } };
        SemanticValidation.CheckReadSnapshots(lateRead, new HashSet<string> { "snapshot" });
        check(lateRead.Problems.Count > 0, "同一块中在使用之后读取不能证明快照有效");
        var conditionalRead = diamond with { Problems = [], Blocks = new(diamond.Blocks)
        {
            [0x104] = diamond.Blocks[0x104] with { Statements = [read] },
            [0x10c] = diamond.Blocks[0x10c] with { Statements = [new ReturnStatement(0x10c, new NameExpression("snapshot"))] }
        }};
        SemanticValidation.CheckReadSnapshots(conditionalRead, new HashSet<string> { "snapshot" });
        check(conditionalRead.Problems.Count > 0, "只有一个前驱读取的字段不能在共同后继直接使用");
        var renamed = SourceTree.Map(sequence, value => value is NameExpression { Name: "snapshot" } ? new NameExpression("captured") : value);
        check(JsonSerializer.Serialize(SemanticData.Function(renamed)).Contains("captured"), "await 子树参与语义遍历及序列化");
        var unknown = SourceTree.Map(sequence, value => value is NameExpression { Name: "snapshot" } ? new UnknownExpression("unbound") : value);
        SemanticValidation.Check(unknown);
        check(unknown.Problems.Any(p => p.Contains("unbound")), "await 包装不能掩盖未知输入");

        var phi = new PhiExpression("joined", "int32_t", [new(0x104, new ConstantExpression(1)), new(0x108, new ConstantExpression(2))]);
        var pending = diamond with { Blocks = diamond.Blocks.ToDictionary(p => p.Key, p => p.Value with { Statements = [.. p.Value.Statements] }), Problems = [] };
        pending.Blocks[0x10c] = pending.Blocks[0x10c] with { Statements =
            [new EvaluateStatement(0x10c, new AwaitExpression(new InvocationExpression("Use", null, [new CastExpression("long", phi)], false))),
             new SetLocalStatement(0x10c, "copy", phi)] };
        SemanticValidation.Check(pending);
        check(pending.Problems.Count == 1 && writer.Raw(pending).Contains("UNRESOLVED_PHI(\"joined\", (0x104, 1), (0x108, 2))"),
            "未降低 Phi 保留前驱和值，并报告为未恢复，诊断输出不崩溃");
        check(JsonSerializer.Serialize(SemanticData.Function(pending)).Contains("unresolved-phi"), "未降低 Phi 的语义证据可以序列化");
        pending.Problems.Clear();
        PhiLowering.Apply(pending);
        SemanticValidation.Check(pending);
        check(pending.Problems.Count == 0 && !writer.Raw(pending).Contains("UNRESOLVED_PHI") &&
            pending.Blocks[0x104].Statements.OfType<SetLocalStatement>().Single().Value == new ConstantExpression(1) &&
            pending.Blocks[0x108].Statements.OfType<SetLocalStatement>().Single().Value == new ConstantExpression(2),
            "公共遍历降低 await、类型转换和边复制中的 Phi，保留前驱对应关系");
    }
}
