using System.Text.Json;
using Cpp2CS.Tests.Metrics;
using Mono.Cecil;

namespace Cpp2CS.Tests.Execution;

internal static class GenericExecutionChecks
{
    public const string Command = "cil-generic-execution";
    private const string Source = """
        public interface I { }
        public class Base { }
        public class Box<T> {
            public T v;
            public T Get() => v;
            public U Echo<U>(T x, U y) => y;
        }
        public class ValueOwner<T> where T : struct {
            public T Get(T x) => x;
            public U Mixed<U>(U x) where U : class => x;
        }
        public class Outer<T> {
            public class Inner<U> {
                public T first;
                public U second;
                public T Read() => first;
                public V Echo<V>(T x, U y, V z) => z;
            }
        }
        public static class Cases {
            public static int Plain(int x) => x;
            public static T Pick<T>(T a, T b) => a;
            public static bool ValueOnly<T>(T x) => x == null;
            public static bool ReferenceOnly<T>(T x) => x == null;
            public static T Value<T>(T x) where T : struct => x;
            public static T Reference<T>(T x) where T : class => x;
            public static T Constructor<T>(T x) where T : new() => x;
            public static T Interface<T>(T x) where T : I => x;
            public static T BaseClass<T>(T x) where T : Base => x;
            public static T Related<T, U>(T x) where T : U => x;
            public static int Array<T>(T[] xs) => xs.Length;
            public static T Default<T>() => default(T);
            public static unsafe int Partial<T>() {
                if (default(T) == null) return 1;
                int* p = stackalloc int[2]; return *p;
            }
            public static unsafe int Unknown<T>() { int* p = stackalloc int[2]; return *p; }
        }
        """;

    public static int Run()
    {
        var a = new Assertions();
        using var left = new CompiledSource(Source);
        using var right = new CompiledSource(Source);
        using var wrong = new CompiledSource(Source
            .Replace("Pick<T>(T a, T b) => a", "Pick<T>(T a, T b) => b", StringComparison.Ordinal)
            // Object 上 default(T) 为 null；Int32 上非 null，右侧因而恒真。
            .Replace("ValueOnly<T>(T x) => x == null", "ValueOnly<T>(T x) => x == null || default(T) != null", StringComparison.Ordinal)
            // Int32 的第一次判空为假，短路后与左侧相同；Object 的 null 输入才有差异。
            .Replace("ReferenceOnly<T>(T x) => x == null", "ReferenceOnly<T>(T x) => x == null && x != null", StringComparison.Ordinal));
        var options = new MetricOptions(32, 10000);
        var factory = CecilModel.Factory(left.Module, right.Module);
        var wrongFactory = CecilModel.Factory(left.Module, wrong.Module);
        MethodMetric Compare(string name, string type = "Cases", bool changed = false) =>
            IlMetrics.Compare(left.Method(type, name), (changed ? wrong : right).Method(type, name), options, changed ? wrongFactory : factory);
        void Rounds(MethodMetric result, bool reference, bool value)
        {
            a.True(result.Instances is { Count: 2 }, "泛型结果保留两轮：" + result.Identity);
            foreach (var (name, applicable) in new[] { ("ref", reference), ("value", value) })
                a.True(result.Instances![name].Applicable == applicable
                    && result.Instances[name].Status == (applicable ? MetricStatus.Match : MetricStatus.Inconclusive)
                    && result.Instances[name].ReasonKind == (applicable ? ComparisonReason.None : ComparisonReason.GenericDefinition),
                    $"约束决定 {name} 轮的适用性和结果：{result.Identity}；{IlMetrics.Json(result.Instances)}");
        }
        var same = Compare("Pick");
        Rounds(same, true, true);
        a.True(same is { Status: MetricStatus.Match, CompletedCases: 64 }, "相同泛型方法的两轮各执行全部请求用例");
        var pick = Compare("Pick", changed: true);
        a.True(pick.Status == MetricStatus.Mismatch, "Pick 的两个实参可区分");
        var valueOnly = Compare("ValueOnly", changed: true);
        var refOnly = Compare("ReferenceOnly", changed: true);
        a.True(valueOnly.Status == MetricStatus.Mismatch && valueOnly.Instances!["ref"].Status == MetricStatus.Match
            && valueOnly.Instances["value"].Status == MetricStatus.Mismatch && valueOnly.Difference!.StartsWith("value 轮：", StringComparison.Ordinal),
            "引用轮一致不能遮住值轮差异：" + IlMetrics.Json(valueOnly));
        a.True(refOnly.Status == MetricStatus.Mismatch && refOnly.Instances!["ref"].Status == MetricStatus.Mismatch
            && refOnly.Instances["value"].Status == MetricStatus.Match && refOnly.Difference!.StartsWith("ref 轮：", StringComparison.Ordinal),
            "引用轮差异后仍完成值轮：" + IlMetrics.Json(refOnly));
        foreach (var result in new[] { valueOnly, refOnly })
            a.True(IlMetrics.Compare(left.Method("Cases", result == valueOnly ? "ValueOnly" : "ReferenceOnly"),
                wrong.Method("Cases", result == valueOnly ? "ValueOnly" : "ReferenceOnly"), options with { Cases = 1, FirstSeed = result.Seed!.Value }, wrongFactory).Status == MetricStatus.Mismatch,
                "差异种子可重现");
        Rounds(Compare("Get", "Box`1"), true, true);
        Rounds(Compare("Echo", "Box`1"), true, true);
        Rounds(Compare("Read", "Outer`1/Inner`1"), true, true);
        Rounds(Compare("Echo", "Outer`1/Inner`1"), true, true);
        Rounds(Compare("Get", "ValueOwner`1"), false, true);
        Rounds(Compare("Value"), false, true);
        Rounds(Compare("Reference"), true, false);
        Rounds(Compare("Constructor"), true, true);
        foreach (var result in new[] { Compare("Interface"), Compare("BaseClass"), Compare("Related"), Compare("Mixed", "ValueOwner`1") })
        {
            Rounds(result, false, false);
            a.True(result is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.GenericDefinition }, "两轮均不适用保留 GenericDefinition");
        }
        Rounds(Compare("Array"), true, true);
        Rounds(Compare("Default"), true, true);
        var partial = Compare("Partial");
        a.True(partial.Status == MetricStatus.Match && partial.Instances!["ref"].Status == MetricStatus.Match
            && partial.Instances["value"].Status == MetricStatus.Inconclusive, "一轮一致且另一轮无法判定时归为一致：" + IlMetrics.Json(partial));
        var unknown = Compare("Unknown");
        a.True(unknown is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.UnsupportedConstruct }
            && unknown.Instances!.Values.All(i => i.Applicable && i.Status == MetricStatus.Inconclusive), "适用轮均无法判定时保留执行原因");
        var json = IlMetrics.Json(IlMetrics.Report([same, valueOnly, refOnly, Compare("Plain")], options));
        using var report = JsonDocument.Parse(json);
        var rows = report.RootElement.GetProperty("methods").EnumerateArray().ToArray();
        a.True(rows.Take(3).All(r => r.GetProperty("instances").GetProperty("value").GetProperty("status").ValueKind == JsonValueKind.String)
            && !rows[3].TryGetProperty("instances", out _), "JSON 分轮记录泛型方法，非泛型方法没有 instances 字段");
        a.True(json == IlMetrics.Json(IlMetrics.Report([Compare("Pick"), Compare("ValueOnly", changed: true), Compare("ReferenceOnly", changed: true), Compare("Plain")], options)), "泛型报告可复现");
        Correspondence(a, left, options);
        using var external = new CompiledSource("public enum Code : short { Zero, One }");
        var lazy = new CecilModel(left.Module);
        var externalEnum = lazy.Type(external.Module.GetType("Code"));
        a.True(Cpp2CS.Model.ManagedTypes.PrimitiveName(Cpp2CS.Model.ManagedTypes.Underlying(externalEnum)) == "Int16",
            "懒加载的外部枚举先填充底层字段，再提供类型视图");
        using var enumEntry = new CompiledSource("public static class Entry { public static int Read(int x) => x; }");
        enumEntry.Method("Entry", "Read").Parameters[0].ParameterType = external.Module.GetType("Code");
        var enumModel = new CecilModel(enumEntry.Module);
        var parameter = enumModel.Method(enumEntry.Method("Entry", "Read")).Method.Parameters[0].Type;
        a.True(Cpp2CS.Model.ManagedTypes.PrimitiveName(Cpp2CS.Model.ManagedTypes.Underlying(parameter)) == "Int16",
            "构建元数据期间新引用的外部枚举也有底层字段");
        Console.WriteLine($"泛型小例子：同体 {same.Status}（ref={same.Instances!["ref"].Status}；value={same.Instances["value"].Status}）；Pick 改动 {pick.Status}；值轮差异 ref={valueOnly.Instances!["ref"].Status},value={valueOnly.Instances["value"].Status}；引用轮差异 ref={refOnly.Instances!["ref"].Status},value={refOnly.Instances["value"].Status}。");
        return a.Finish(Command);
    }

    private static void Correspondence(Assertions a, CompiledSource left, MetricOptions options)
    {
        using var renamed = new CompiledSource(Source.Replace("static T Pick<T>(T a, T b)", "static U Pick<U>(U a, U b)", StringComparison.Ordinal));
        a.True(IlMetrics.Compare(left.Method("Cases", "Pick"), renamed.Method("Cases", "Pick"), options).Status == MetricStatus.Match, "类型参数按位置对应，允许名称不同");
        using var constraint = new CompiledSource(Source.Replace("Value<T>(T x) where T : struct", "Value<T>(T x) where T : class", StringComparison.Ordinal));
        using var ownerConstraint = new CompiledSource(Source.Replace("class ValueOwner<T> where T : struct", "class ValueOwner<T> where T : class", StringComparison.Ordinal));
        using var fields = new CompiledSource(Source.Replace("public T v;", "public T v; public int extra;", StringComparison.Ordinal));
        foreach (var (l, r) in new[] {
            (left.Method("Cases", "Value"), constraint.Method("Cases", "Value")),
            (left.Method("ValueOwner`1", "Get"), ownerConstraint.Method("ValueOwner`1", "Get")),
            (left.Method("Box`1", "Get"), fields.Method("Box`1", "Get")) })
        {
            var result = IlMetrics.Compare(l, r, options);
            a.True(result is { Status: MetricStatus.Inconclusive, ReasonKind: ComparisonReason.TypeMismatch }
                && result.Instances!.Values.All(i => i.ReasonKind == ComparisonReason.TypeMismatch), "代入前后仍严格核对泛型约束与字段：" + IlMetrics.Json(result));
        }
        var abstractMethod = renamed.Method("Cases", "Interface");
        abstractMethod.Attributes |= MethodAttributes.Abstract;
        var noBody = IlMetrics.Compare(abstractMethod, abstractMethod, options);
        a.True(noBody.ReasonKind == ComparisonReason.MissingBody && noBody.Instances!.Values.All(i => !i.Applicable), "声明无体优先保留 MissingBody，并记录不适用性");
        var applicableNoBody = renamed.Method("Cases", "Pick");
        applicableNoBody.Attributes |= MethodAttributes.Abstract;
        var missingBody = IlMetrics.Compare(applicableNoBody, applicableNoBody, options);
        a.True(missingBody.ReasonKind == ComparisonReason.MissingBody && missingBody.Instances!.Values.All(i => i.Applicable), "适用但声明无体时分轮保留 MissingBody");
    }
}
