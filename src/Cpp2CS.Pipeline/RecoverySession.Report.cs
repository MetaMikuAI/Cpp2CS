using System.Diagnostics;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;

namespace Cpp2CS.Pipeline;

public static partial class RecoverySession
{
    private static readonly JsonSerializerOptions Json = new() { Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping };
    private static StringBuilder Report(MethodRecoveryResult[] results, List<MethodRecoveryResult> emitted,
        Dictionary<MethodRecoveryResult, string> emitProblems, Dictionary<ulong, long> bytes)
    {
        long Bytes(IEnumerable<MethodRecoveryResult> rows) => rows.Select(r => r.Entry).Distinct().Sum(e => bytes[e]);
        var total = Bytes(results);
        double Fraction(long size) => (double)size / Math.Max(1, total);
        var recovered = results.Where(r => r.Body is not null).ToArray();
        var report = new StringBuilder();
        report.AppendLine($"方法 {results.Length}（字节 {total}）：L3 无洞 {recovered.Length}（{(double)recovered.Length / Math.Max(1, results.Length):P1}，字节 {Fraction(Bytes(recovered)):P2}），写出 CIL {emitted.Count}（{(double)emitted.Count / Math.Max(1, results.Length):P1}，字节 {Fraction(Bytes(emitted)):P2}）");
        report.AppendLine("字节均按入口去重；各桶会重叠，不可直接相加。并集用于对账；“仅此”只看独立洞。");
        var declarations = results.Where(r => r.Declaration is not null).ToArray();
        report.AppendLine($"运行时声明已核验：{declarations.Length} 方法 / {Bytes(declarations)} 原生字节（未恢复为 CIL 方法体，不计入字节覆盖率）");
        var buckets = results.Where(r => r.Body is null && r.Declaration is null).Select(r => (Result: r,
            Categories: r.Holes.Where(h => !h.Derived).Select(h => Category(h.Reason)).Distinct().ToArray())).ToArray();
        report.AppendLine($"状态对账：洞 {buckets.Length} / {Bytes(buckets.Select(b => b.Result))} 字节；写出失败 {emitProblems.Count} / {Bytes(emitProblems.Keys)} 字节；已写出 {emitted.Count} / {Bytes(emitted)} 字节；运行时声明 {declarations.Length} / {Bytes(declarations)} 字节；入口并集 {bytes.Count} / {total} 字节");
        report.AppendLine();
        report.AppendLine("独立洞分桶：方法数 / 字节数 / 仅此方法数 / 仅此字节数 / 连带洞条数 / 桶");
        var derived = results.SelectMany(r => r.Holes).Where(h => h.Derived).GroupBy(h => Category(h.Reason)).ToDictionary(g => g.Key, g => g.Count());
        foreach (var group in buckets.SelectMany(b => b.Categories.Select(c => (Category: c, b.Result, Only: b.Categories.Length == 1)))
            .GroupBy(x => x.Category).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal))
        {
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(x => x.Result)),10} {group.Count(x => x.Only),7} {Bytes(group.Where(x => x.Only).Select(x => x.Result)),10} {derived.GetValueOrDefault(group.Key),8}  {group.Key}");
            foreach (var reason in group.SelectMany(x => x.Result.Holes.Where(h => !h.Derived && Category(h.Reason) == group.Key).Select(h => h.Reason)).GroupBy(r => r).OrderByDescending(r => r.Count()).Take(4))
                report.AppendLine($"           {reason.Count(),6}  {Shorten(reason.Key)}");
            derived.Remove(group.Key);
        }
        foreach (var (category, count) in derived.OrderBy(p => p.Key, StringComparer.Ordinal))
            report.AppendLine($"  {0,7} {0,10} {0,7} {0,10} {count,8}  {category}");
        report.AppendLine($"独立洞并集：{buckets.Count(b => b.Categories.Length > 0)} 方法 / {Bytes(buckets.Where(b => b.Categories.Length > 0).Select(b => b.Result))} 字节");

        bool Incomplete(string category) => category is "泛型" or "签名" or "提升" or "L2";
        var incomplete = buckets.Where(b => b.Categories.Any(Incomplete)).ToArray();
        report.AppendLine();
        report.AppendLine($"不可继续：{incomplete.Length} 方法 / {Bytes(incomplete.Select(b => b.Result))} 字节（泛型、签名、提升、L2 错误；洞集合不完整，不参与解锁与贪心）");
        foreach (var group in incomplete.SelectMany(b => b.Categories.Where(Incomplete).Select(c => (Category: c, b.Result))).GroupBy(x => x.Category))
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(x => x.Result)),10}  {group.Key}");

        // L3 无洞而写出失败的空集合不能被算作任意桶的收益：把已知 L4 障碍作为单独的桶。
        var candidates = buckets.Where(b => b.Categories.Length > 0 && !b.Categories.Any(Incomplete))
            .Concat(emitProblems.Select(p => (Result: p.Key, Categories: new[] { "CIL/" + Category(p.Value) }))).ToArray();
        var categories = candidates.SelectMany(b => b.Categories).Distinct().Order(StringComparer.Ordinal).ToArray();
        var alreadyEmitted = emitted.Select(r => r.Entry).ToHashSet();
        long UnlockBytes(IEnumerable<MethodRecoveryResult> rows) => Bytes(rows.Where(r => !alreadyEmitted.Contains(r.Entry)));
        report.AppendLine();
        report.AppendLine("可解锁量（诊断上限；不含已写出入口的字节，修洞后仍可能暴露新洞或写出失败）：");
        report.AppendLine("只差这一桶：方法数 / 新增字节数 / 桶（CIL/ 前缀表示已知写出障碍）");
        foreach (var category in categories.Select(c => (Name: c, Rows: candidates.Where(b => b.Categories.All(x => x == c)).Select(b => b.Result).ToArray()))
            .OrderByDescending(c => UnlockBytes(c.Rows)).ThenBy(c => c.Name, StringComparer.Ordinal))
            report.AppendLine($"  {category.Rows.Length,7} {UnlockBytes(category.Rows),10}  {category.Name}");
        report.AppendLine("按字节贪心清桶（并列按桶名序数排序）：步 / 新清桶 / 累计方法数 / 累计新增字节数 / 范围字节占比");
        var cleared = new HashSet<string>();
        for (var step = 1; step <= Math.Min(10, categories.Length); step++)
        {
            var choice = categories.Where(c => !cleared.Contains(c)).Select(c => (Name: c,
                Rows: candidates.Where(b => b.Categories.All(x => x == c || cleared.Contains(x))).Select(b => b.Result).ToArray()))
                .OrderByDescending(c => UnlockBytes(c.Rows)).ThenBy(c => c.Name, StringComparer.Ordinal).First();
            cleared.Add(choice.Name);
            report.AppendLine($"  {step,2} {choice.Name}  {choice.Rows.Length,7} {UnlockBytes(choice.Rows),10} {Fraction(UnlockBytes(choice.Rows)):P2}");
        }
        report.AppendLine();
        report.AppendLine("CIL 写出失败：方法数 / 字节数 / 桶");
        foreach (var group in emitProblems.GroupBy(p => Category(p.Value)).OrderByDescending(g => g.Count()))
            report.AppendLine($"  {group.Count(),7} {Bytes(group.Select(p => p.Key)),10}  {group.Key}  例：{Shorten(group.First().Value)}");
        return report;
    }

    /// <summary>方法体用到的构造，用于挑选竖切集合和覆盖统计。loop 为深度优先遍历中的回边。</summary>
    private static string[] Features(ManagedBody body)
    {
        var features = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var region in body.Regions) features.Add(region.Kind == ManagedRegionKind.Catch ? "eh-catch" : "eh-fault");
        if (body.Method.Method.Name == ".ctor") features.Add("ctor");
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            var feature = statement switch
            {
                ManagedStore { Target: FieldValue } => "field-store", ManagedStore { Target: StaticFieldValue } => "static-store",
                ManagedStore { Target: ArrayElementValue } => "array-store",
                ManagedCall c => c.Invocation.Virtual ? "callvirt" : "call",
                ManagedBranch => "branch", ManagedSwitch => "switch", ManagedThrow => "throw", ManagedRethrow => "rethrow", ManagedEndFault => "fault", ManagedHole => "hole", ManagedCheck => "check", ManagedReturn { Value: not null } => "return-value",
                _ => null,
            };
            if (feature is not null) features.Add(feature);
            var values = statement switch
            {
                // 写入目标本身不是读取
                ManagedStore s => ManagedValues.Children(s.Target).Append(s.Value),
                ManagedJump or ManagedBranch or ManagedSwitch => ManagedValues.CopiedValues(statement).Concat(ManagedValues.Of(statement)),
                _ => ManagedValues.Of(statement),
            };
            foreach (var value in values.SelectMany(ManagedValues.Walk))
            {
                feature = value switch
                {
                    FieldValue => "field-load", StaticFieldValue => "static-load", NewObjectValue => "newobj", DelegateValue => "delegate-new", NewArrayValue => "newarr",
                    ArrayElementValue => "array-load", ArrayLengthValue => "array-length", StringValue => "string", BoxValue => "box",
                    IsInstValue => "isinst", UnboxAddressValue => "unbox", BinaryValue => "arith", ConversionValue => "convert", ChoiceValue => "select", ComparisonValue => "compare",
                    _ => null,
                };
                if (feature is not null) features.Add(feature);
                if (ManagedTypes.PrimitiveName(value.Type) is "Single" or "Double") features.Add("float");
            }
        }
        if (body.Blocks.Select(b => b.Address).Distinct().Count() != body.Blocks.Count)
        {
            features.Add("invalid-control-flow");
            return features.ToArray();
        }
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        if (body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges).Any(e => !blocks.ContainsKey(e.Target)))
        {
            features.Add("invalid-control-flow");
            return features.ToArray();
        }
        var state = new Dictionary<ulong, bool>(); // false：在栈上，true：已完成
        bool Loop(ulong address)
        {
            state[address] = false;
            foreach (var target in blocks[address].Statements.SelectMany(s => ManagedValues.Edges(s).Select(e => e.Target)))
                if (state.TryGetValue(target, out var done) ? !done : Loop(target)) return true;
            state[address] = true;
            return false;
        }
        if (Loop(body.Blocks[0].Address)) features.Add("loop");
        return features.ToArray();
    }

    private static TypeDef Top(TypeDef type)
    {
        while (type.DeclaringType is not null) type = type.DeclaringType;
        return type;
    }

    private static bool InNamespaces(TypeDef type, string[] namespaces)
    {
        var ns = Top(type).Namespace;
        return namespaces.Any(n => ns == n || ns.StartsWith(n + ".", StringComparison.Ordinal));
    }

    private static string Category(string reason) => reason.Split(' ')[0];

    private static string Shorten(string text) => text.Length > 150 ? text[..150] + "…" : text;
}
