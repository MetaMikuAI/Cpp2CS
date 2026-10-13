using System.Text.Json;
using Cpp2CS.Native;

public static class ArithmeticArrayChecks
{
    public static void Run(Action<bool, string> check)
    {
        foreach (var (input, expected) in new (double, int)[] { (1.25, 2), (-1.25, -1), (0, 0), (-0.0, 0),
            (double.NaN, 0), (double.PositiveInfinity, int.MaxValue), (double.NegativeInfinity, int.MinValue),
            (2147483648d, int.MaxValue), (-2147483649d, int.MinValue), (2147483646.25, int.MaxValue), (double.Epsilon, 1) })
            check(NumericSemantics.CeilingToInt32(input) == expected, $"FCVTPS Int32 数值边界 {input}");
        check(NumericSemantics.CeilingToInt64(double.PositiveInfinity) == long.MaxValue &&
            NumericSemantics.CeilingToInt64(double.NegativeInfinity) == long.MinValue && NumericSemantics.CeilingToInt64(double.NaN) == 0,
            "FCVTPS Int64 饱和与 NaN");
        var method = new NativeMethod(0x100, "Example$$Numeric", "int32_t", [], "");
        var graph = new NativeGraph([new(0x100, "ret", "", [], false, false, "")], _ => false);
        var invalid = new LiftResult(method, [], new() { [0x100] = new(0x100, [new ReturnStatement(0x100,
            new OperationExpression(ValueOperation.FloatToSignedCeiling, "int32_t", [new UnknownExpression("missing-float")]))], null, []) }, [], [], graph);
        SemanticValidation.Check(invalid);
        check(invalid.Problems.Any(p => p.Contains("missing-float")), "类型化数值节点不能隐藏未知输入");
        var read = new MemberExpression(new NameExpression("source"), new("Value", "int32_t", 16, 4, "Object"), "Value", "int");
        var captured = new CapturedExpression("loaded", read);
        var eager = invalid with { Problems = [], Blocks = new() { [0x100] = new(0x100,
            [new AssignStatement(0x100, "loaded", read, "int32_t"), new ReturnStatement(0x104,
                new OperationExpression(ValueOperation.Select, "int32_t", [new NameExpression("condition"), captured, new ConstantExpression(0)]))], null, []) } };
        check(ViewNormalizer.Normalize(eager).Blocks[0x100].Statements[0] is AssignStatement, "CSEL 两侧已求值的读取不能移入惰性三元分支");
        var reference = new NativeValue(new Cpp2CS.IR.InputBits("object", 64), "Example_o*", new NameExpression("item"));
        var zero = new NativeValue(Cpp2CS.IR.BitOps.Constant(0, 64), "int64_t", new ConstantExpression(0));
        var selection = NativeValues.ReferenceSelection(reference, zero);
        check(selection is { Type: "Example_o*", Right: NameExpression { Name: "null" } }, "引用与明确的零位模式选择保留引用类型和 null");
        check(NativeValues.ReferenceSelection(reference, reference) is { Type: "Example_o*" } &&
            NativeValues.ReferenceSelection(reference, zero with { Bits = new Cpp2CS.IR.InputBits("loop", 64), Expression = new NameExpression("loop") }) is null,
            "引用选择不能把未定整数循环值强转为对象或把对象强转为 long");
        var referenceRead = read with { Field = read.Field with { Type = "Example_o*", Size = 8 }, ManagedType = "Example" };
        var referenceBody = eager with { Blocks = new() { [0x100] = new(0x100,
            [new AssignStatement(0x100, "loaded", referenceRead, "Example_o*"), new ReturnStatement(0x104,
                new OperationExpression(ValueOperation.ReferenceSelect, "Example_o*", [new NameExpression("condition"),
                    new CapturedExpression("loaded", referenceRead), new NameExpression("null")]))], null, []) } };
        check(ViewNormalizer.Normalize(referenceBody).Blocks[0x100].Statements[0] is AssignStatement &&
            SemanticWriter.Expression(new OperationExpression(ValueOperation.ReferenceSelect, "Example_o*",
                [new NameExpression("condition"), new NameExpression("item"), new NameExpression("null")])) == "(condition ? item : null)",
            "引用选择输出保留对象身份，字段读取仍先于惰性分支求值");
    }
    public static void Native(Action<bool, string> check, string config)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!);
        var result = session.Recover(0x570e728);
        session.Save(result, "artifacts/recovered");
        check(result.Problems.Count == 0, "真实浮点与数组方法无未知语义");
        var text = new SemanticWriter(session.Symbols).Structured(session.View(result));
        check(!text.Contains("UNKNOWN") && !text.Contains("UNRESOLVED") && !text.Contains("Runtime.Bits"), "结构体参数和数值结果不保留未解析位片段");
        check(!text.Contains(".m_Items") && result.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>()
            .Any(c => c.Name == "Runtime.GCWriteBarrier" && c.Arguments is [AddressOfExpression { Target: OperationExpression { Operation: ValueOperation.ArrayElement } }]),
            "数组访存写回后的写屏障指向元素地址");
        check(text.Contains("staminaData.boost") && result.Blocks.Values.SelectMany(b => b.Statements).OfType<AssignStatement>()
            .Any(a => a.Value is OperationExpression { Operation: ValueOperation.Add }), "结构体字段来源与累计 boost 加法保留");
        var assignments = result.Blocks.Values.SelectMany(b => b.Statements).OfType<AssignStatement>().ToArray();
        check(assignments.Select(a => a.Name).Distinct().Count() == assignments.Length, "成对加载产生唯一值身份");
        foreach (var pc in new ulong[] { 0x570e918, 0x570e92c })
            check(assignments.Where(a => a.Address == pc).Select(a => a.Value).OfType<MemberExpression>().Select(m => m.Field.Offset).Distinct().Count() == 2,
                $"0x{pc:x} 的两个字段保持独立");
        Directory.CreateDirectory("artifacts/ArithmeticFixture");
        File.WriteAllText("artifacts/ArithmeticFixture/ArithmeticFixture.csproj", """
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net10.0</TargetFramework><ImplicitUsings>enable</ImplicitUsings><Nullable>annotations</Nullable></PropertyGroup>
              <ItemGroup><ProjectReference Include="../../src/Cpp2CS.Core/Cpp2CS.Core.csproj" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText("artifacts/ArithmeticFixture/Program.cs", Fixture.Replace("/* RECOVERED METHOD */", text));
    }
    private const string Fixture = """
        using Cpp2CS.Native;
        using Sekai;
        public class Fixture
        {
            TextView messageBodyTextMesh = new();
            Changer liveBoostNumberChanger = new();
            object _beforeNormalStaminaView = new(), _beforeBoostStaminaView = new(), _beforeWarningMessage = new();
            object _afterNormalStaminaView = new(), _afterBoostStaminaView = new(), _afterWarningMessage = new();
            List<(object Normal, object Boost, object Warning, int Amount)> calls = [];
            static object MetadataSlot(string name) => name;
            static object MetadataValue(string name) => name;
            void UpdateStaminaView(object normal, object boost, object warning, int amount) => calls.Add((normal, boost, warning, amount));
            /* RECOVERED METHOD */
            public static void Main(string[] args)
            {
                foreach (var (amount, recovery, old, expected) in new (int, int, int, int)[] {
                    (7, 3, 5, 3), (-7, 3, 5, -2), (0, 0, 5, 0), (1, 0, 5, int.MinValue),
                    (-1, 0, 5, int.MinValue), (int.MaxValue, 1, 1, int.MaxValue), (int.MinValue, 1, 1, int.MinValue) })
                {
                    var fixture = new Fixture();
                    CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Recovery.recoveryBoostStamina = recovery;
                    CP.SingletonMonoBehaviour<UserDataManager>.Instance.UserMysekaiStamina.boostStamina = old;
                    fixture.Initialize(new() { normal = 91, enhance = 92, boost = amount });
                    if (WordingManager.LastValue != expected || fixture.messageBodyTextMesh.Value != expected.ToString()) throw new Exception("浮点或装箱结果错误");
                    if (fixture.liveBoostNumberChanger.Pair != (old, unchecked(old + amount))) throw new Exception("累计参数错误");
                    if (fixture.calls.Count != 2 || fixture.calls[0] != (fixture._beforeNormalStaminaView, fixture._beforeBoostStaminaView, fixture._beforeWarningMessage, old) ||
                        fixture.calls[1] != (fixture._afterNormalStaminaView, fixture._afterBoostStaminaView, fixture._afterWarningMessage, unchecked(old + amount))) throw new Exception("视图参数混淆");
                }
                Console.WriteLine("PASS: generated method compiles; 7 numeric scenarios, boxed array content, sum and both view argument lists match (stub runtime)");
                if (args.Length == 1)
                {
                    using var oracle = System.Text.Json.JsonDocument.Parse(File.ReadAllText(args[0]));
                    foreach (var row in oracle.RootElement.EnumerateArray())
                    {
                        var amount = row.GetProperty("amount").GetInt32();
                        var recovery = row.GetProperty("recovery").GetInt32();
                        var expected = row.GetProperty("expected").GetInt32();
                        CP.SingletonMonoBehaviour<MasterDataManager>.Instance.Recovery.recoveryBoostStamina = recovery;
                        CP.SingletonMonoBehaviour<UserDataManager>.Instance.UserMysekaiStamina.boostStamina = 5;
                        var fixture = new Fixture();
                        fixture.Initialize(new() { boost = amount });
                        if (WordingManager.LastValue != expected) throw new Exception($"ARM64 mismatch: {amount}/{recovery}: {WordingManager.LastValue} != {expected}");
                    }
                    Console.WriteLine($"PASS: generated method agrees with {oracle.RootElement.GetArrayLength()} independently emulated ARM64 numeric cases");
                }
            }
        }
        public class TextView { public string Value = ""; public void SetText(string value, bool flag) { if (flag) throw new Exception(); Value = value; } }
        public class Changer { public (int, int) Pair; public void SetUp(int before, int after) => Pair = (before, after); }
        public static class Runtime
        {
            static byte flag;
            public static ref byte Global(ulong address) => ref flag;
            public static void EnsureMetadataInitialized(ulong flag, params object[] slots) { }
            public static void InitializeMetadata(object slot) { }
            public static void EnsureClassInitialized(object type) { }
            public static object Box<T>(T value) where T : struct => value;
            public static Type ClassOf(object value) => value.GetType();
            public static Type ElementClass(Type type) => type.GetElementType()!;
            public static object? IsInstance(object value, Type type) => type.IsInstanceOfType(value) ? value : null;
            public static Exception CreateArrayTypeMismatchException() => new ArrayTypeMismatchException();
            public static void RaiseException(Exception exception) => throw exception;
            public static void GCWriteBarrier(ref object slot) { }
        }
        namespace CP { public static class SingletonMonoBehaviour<T> where T : new() { public static T Instance = new(); } }
        namespace Sekai
        {
            public class MasterDataManager { public Recovery Recovery = new(); public Recovery GetMasterMysekaiStaminaRecovery() => Recovery; }
            public class Recovery { public int recoveryBoostStamina; }
            public class UserDataManager { public Stamina UserMysekaiStamina = new(); }
            public class Stamina { public int boostStamina; }
            public static class WordingManager { public static int LastValue; public static string GetFormat(string key, object[] values) { if (key != "MSG_BOOST_STAMINA_RECOVER_CONFIRM" || values.Length != 1) throw new Exception(); LastValue = (int)values[0]; return LastValue.ToString(); } }
        }
        namespace Sekai.Mysekai { public struct StaminaData { public int normal, enhance, boost; } }
        """;
}
