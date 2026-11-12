using Cpp2CS.Tests.Execution;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests.Metrics;

internal static class MetricChecks
{
    public const string Command = "il-metrics-check";
    private const string Source = """
        public static class Cases {
            public static int Field;
            public static int Switch(int x) => x;
            public static int Constant(int x) => x + 7;
            public static int Branch(int x) => x > 0 ? 13 : 17;
            public static int Add(int x) => x + 3;
            public static int Write(int x) { Field = x; return x; }
            public static int Call(int x) => Target(x, 3);
            public static int Target(int a, int b) => a - b;
            public static int Return(int x) => 7;
            public static int Over(int x) => x;
            public static long Over(long x) => x;
            public static T Generic<T>(T x) => x;
            public static int Loop(int x) { while (true) x++; }
            public static double Nan(double x) => x / x;
            public static double AllNan(double x) => (x - x) / (x - x);
        }
        """;
    public static int Run()
    {
        var a = new Assertions();
        using var left = new CompiledSource(Source);
        using var right = new CompiledSource(Source);
        var options = new MetricOptions(32, 1000);
        foreach (var source in new[] { left, right })
        {
            var body = source.Method("Cases", "Switch").Body;
            body.Instructions.Clear();
            var tail = Instruction.Create(OpCodes.Ldc_I4, 5);
            body.Instructions.Add(Instruction.Create(OpCodes.Ldarg_0));
            body.Instructions.Add(Instruction.Create(OpCodes.Switch, new[] { tail, tail }));
            body.Instructions.Add(tail); body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        }
        var switchCoverage = IlMetrics.Compare(left.Method("Cases", "Switch"), right.Method("Cases", "Switch"), options with { Cases = 128 });
        a.True(switchCoverage.Coverage!.Branches.Single().Directions.SequenceEqual(new[] { true, true, true }), "switch 重复目标仍分别记录索引与默认出口");
        MethodMetric Compare(string name) => IlMetrics.Compare(left.Method("Cases", name), right.Method("Cases", name), options);
        a.True(Compare("Branch").Coverage is { Complete: true }, "双向分支和指令覆盖完整");
        a.True(IlMetrics.Compare(left.Method("Cases", "Constant"), right.Method("Cases", "Constant"), new(1, 7)).ReasonKind == ComparisonReason.StepBudget, "两侧共享一个用例步数预算");
        a.True(Compare("Constant").Status == MetricStatus.Match, "一致状态");
        a.True(IlMetrics.Compare(left.Method("Cases", "Constant"), null, options).Status == MetricStatus.NotWritten, "没写出状态");
        var withoutBody = right.Method("Cases", "Return");
        var savedAttributes = withoutBody.Attributes; withoutBody.Attributes |= MethodAttributes.Abstract;
        a.True(IlMetrics.Compare(left.Method("Cases", "Return"), withoutBody, options).Status == MetricStatus.NotWritten, "待测没有方法体");
        withoutBody.Attributes = savedAttributes;
        var savedBody = withoutBody.Body; withoutBody.Body = new MethodBody(withoutBody);
        a.True(IlMetrics.Compare(left.Method("Cases", "Return"), withoutBody, options).Status == MetricStatus.NotWritten, "空指令体视为没写出");
        withoutBody.Body = savedBody;
        a.True(Compare("Generic") is { Status: MetricStatus.Match, Instances.Count: 2 }, "泛型定义分轮对照");
        a.True(Compare("Loop") is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.StepBudget }, "步数预算");
        a.True(Compare("Nan") is { Status: MetricStatus.Match, CompletedCases: > 0, NaNSkippedCases: > 0 }, "部分 NaN 跳过后仍判定");
        a.True(Compare("AllNan") is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.NaN, CompletedCases: 0, NaNSkippedCases: 32 }, "全 NaN");
        var methods = left.Module.GetType("Cases").Methods.Where(m => m.Name == "Over").ToArray();
        var report = IlMetrics.Compare(left.Module, right.Module, methods, options);
        a.True(report.Methods.Length == 2 && report.Methods.All(m => m.Status == MetricStatus.Match), "重载按完整身份对应");
        a.True(IlMetrics.Json(report) == IlMetrics.Json(IlMetrics.Compare(left.Module, right.Module, methods, options)), "报告逐字节确定");
        var examples = new Dictionary<MutationKind, string> { [MutationKind.IntegerConstant] = "Constant", [MutationKind.InvertBranch] = "Branch",
            [MutationKind.AddSubtract] = "Add", [MutationKind.RemoveFieldWrite] = "Write", [MutationKind.RemoveCall] = "Call",
            [MutationKind.DefaultReturn] = "Return", [MutationKind.SwapArguments] = "Call" };
        foreach (var (kind, name) in examples)
        {
            var l = left.Method("Cases", name); var r = right.Method("Cases", name);
            var mutation = Mutations.Generate(r).Single(m => m.Kind == kind);
            var original = r.Body;
            r.Body = Mutations.Changed(r, mutation);
            var found = IlMetrics.Compare(l, r, options);
            a.True(found.Status == MetricStatus.Mismatch && found.Seed is not null, $"{kind} 被发现：{found.Status} {found.Difference}");
            if (found.Seed is { } seed)
                a.True(IlMetrics.Compare(l, r, options with { Cases = 1, FirstSeed = seed }).Status == MetricStatus.Mismatch, $"{kind} 种子重现");
            // 显式不可达块：改动仍存在，但入口直接跳到相同结局。
            Bypass(l.Body); Bypass(r.Body);
            var unseen = IlMetrics.Compare(l, r, options);
            a.True(unseen.Status == MetricStatus.Match && unseen.Coverage!.Unvisited.Contains(mutation.Offset), $"{kind} 未执行位置不误报");
            // 当前例子结束后只恢复插入的入口和尾部，原指令身份保持不变。
            l.Body.Instructions.RemoveAt(0);
            l.Body.Instructions.RemoveAt(l.Body.Instructions.Count - 1);
            l.Body.Instructions.RemoveAt(l.Body.Instructions.Count - 1);
            r.Body = original;
        }
        Correspondence(a, options);
        return a.Finish("IL 指标快速检查");
    }
    private static void Correspondence(Assertions a, MetricOptions options)
    {
        const string source = """
            public class Payload { public int Value; public static int Global; }
            public static class Entry {
                public static int Pure(int x) => x + 1;
                public static int Read(Payload p) => p.Value;
                public static int New() => new Payload().Value;
                public static int Static() => Payload.Global;
            }
            """;
        using var left = new CompiledSource(source);
        using var right = new CompiledSource(source.Replace("public int Value;", "public int Value; public int Extra;", StringComparison.Ordinal));
        MethodMetric Compare(string name) => IlMetrics.Compare(left.Method("Entry", name), right.Method("Entry", name), options);
        a.True(Compare("Pure").Status == MetricStatus.Match, "不相干类型的字段差异不影响纯方法");
        foreach (var name in new[] { "Read", "New", "Static" })
        {
            var result = Compare(name);
            a.True(result is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.TypeMismatch }
                && result.Difference!.Contains("Payload", StringComparison.Ordinal)
                && result.Difference.Contains("字段", StringComparison.Ordinal), "实际使用的类型字段差异指出类型和种类：" + name);
        }
        using var extraMethod = new CompiledSource(source.Replace("public int Value;", "public int Value; public int Unused() => 2;", StringComparison.Ordinal));
        a.True(IlMetrics.Compare(left.Method("Entry", "Read"), extraMethod.Method("Entry", "Read"), options).Status == MetricStatus.Match,
            "未调用的非虚方法不参与字段布局对应");
    }
    private static void Bypass(MethodBody body)
    {
        var tail = Instruction.Create(OpCodes.Ldc_I4, 29);
        body.Instructions.Insert(0, Instruction.Create(OpCodes.Br, tail));
        body.Instructions.Add(tail); body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
}
