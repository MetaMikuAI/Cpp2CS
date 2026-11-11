using System.Text.Json;

namespace Cpp2CS.Tests;

internal static class RuntimeCatalogTruthChecks
{
    public const string Command = "runtime-catalog-truth";
    public static int Run()
    {
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(truth)) { Console.WriteLine("运行时目录定向检查跳过：未设置 CPP2CS_CORPUS_TRUTH"); return 0; }
        var inline = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_INLINE_TRUTH") ?? truth + "-inline";
        var checks = new Assertions();
        using var cases = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "cases.json")));
        var caseNames = cases.RootElement.EnumerateArray().Select(c => c.GetProperty("mapping").GetProperty("cpp_name").GetString()!).ToHashSet(StringComparer.Ordinal);
        using var mappings = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, "mappings.json")));
        foreach (var catalog in RuntimeCatalogChecks.Paths().Select(RuntimeCatalogChecks.Load))
        {
            var target = catalog.Triple switch { "aarch64-linux-android" => "arm64-v8a", "x86_64-linux-android" => "x86_64", _ => throw new InvalidDataException("未支持的语料目标") };
            using var functions = JsonDocument.Parse(File.ReadAllText(Path.Combine(truth, $"functions.{target}.json")));
            var symbols = functions.RootElement.EnumerateArray().GroupBy(f => f.GetProperty("name").GetString()!).ToDictionary(g => g.Key, g => g.First());
            var mangled = catalog.Functions.Select(f => f.MangledName).ToHashSet(StringComparer.Ordinal);
            HashSet<string> inlineNames;
            using (var records = JsonDocument.Parse(File.ReadAllText(Path.Combine(inline, $"inlines.{target}.json"))))
                inlineNames = records.RootElement.EnumerateArray().SelectMany(f => f.GetProperty("records").EnumerateArray())
                    .Select(r => r.GetProperty("linkage_name").GetString()).OfType<string>().ToHashSet(StringComparer.Ordinal);
            foreach (var function in catalog.Functions.Where(f => f.Recognition.Import is not null))
            {
                var imported = functions.RootElement.EnumerateArray().Any(f => f.GetProperty("name").GetString() == function.Recognition.Import && !f.GetProperty("defined").GetBoolean());
                Console.WriteLine($"{target} 导入 {function.MangledName}：{(imported ? "存在" : "不存在")}；不返回={function.Operation.DoesNotReturn}");
                checks.True(function.Recognition.Import == function.MangledName, "导入名精确对应");
            }
            var present = 0;
            foreach (var function in catalog.Functions)
            {
                if (symbols.ContainsKey(function.MangledName)) { present++; continue; }
                // 不存在不等于已经证明内联：声明与调试真值分别给证据。
                Console.WriteLine($"{target} 无独立符号 {function.MangledName}：" +
                    (inlineNames.Contains(function.MangledName) ? "DWARF 有同修饰名内联实例（正面证据）" : function.Declaration.Contains("inline", StringComparison.Ordinal) || function.Declaration.Contains("IL2CPP_FORCE_INLINE", StringComparison.Ordinal)
                        ? "头文件内联入口；不能仅由缺符号断言已内联" : "未发射、裁剪或合并的原因未由函数真值证明"));
            }
            using var audit = JsonDocument.Parse(File.ReadAllText(Path.Combine(inline, $"inline-audit.{target}.json")));
            var mapped = mappings.RootElement.EnumerateArray().Where(m => m.GetProperty("method_id").ValueKind != JsonValueKind.Null).SelectMany(m => m.GetProperty("targets").GetProperty(target).EnumerateArray()).ToArray();
            var managedAddresses = mapped.Select(m => m.GetProperty("address").GetString()!).ToHashSet(StringComparer.Ordinal);
            var managedNames = mapped.Select(m => m.GetProperty("symbol_name").GetString()!).ToHashSet(StringComparer.Ordinal);
            var all = audit.RootElement.EnumerateArray().Where(a => managedAddresses.Contains(a.GetProperty("address").GetString()!))
                .GroupBy(a => a.GetProperty("address").GetString()!).Select(g => g.First()).ToArray();
            var direct = all.SelectMany(a => a.GetProperty("direct_calls").EnumerateArray())
                .GroupBy(c => c.GetProperty("address").GetString()!).Select(g => g.First()).ToArray();
            bool RuntimeTarget(JsonElement call) => !managedAddresses.Contains(call.GetProperty("target").GetString()!) &&
                !call.GetProperty("names").EnumerateArray().Any(n => managedNames.Contains(n.GetString()!));
            bool Covered(JsonElement call) => call.GetProperty("names").EnumerateArray().Any(n => mangled.Contains(n.GetString()!));
            var runtime = direct.Where(RuntimeTarget).ToArray();
            var targets = runtime.GroupBy(c => c.GetProperty("target").GetString()!).ToArray();
            Console.WriteLine($"{target} 全语料：映射函数地址={managedAddresses.Count}；审计函数={all.Length}；无审计={managedAddresses.Count - all.Length}；直接调用点={direct.Length}；运行时调用点={runtime.Length}；目录调用点={runtime.Count(Covered)}；运行时目标={targets.Length}；目录目标={targets.Count(g => g.Any(Covered))}");
            foreach (var group in targets.Where(g => !g.Any(Covered)).OrderByDescending(g => g.Count()).ThenBy(g => g.Key, StringComparer.Ordinal).Take(50))
            {
                var names = group.SelectMany(c => c.GetProperty("names").EnumerateArray()).Select(n => n.GetString()!).Distinct().Order(StringComparer.Ordinal).ToArray();
                var label = names.Length == 0 ? "无符号@" + group.Key : string.Join(" / ", names.Select(n => Demangled(n, symbols)));
                Console.WriteLine($"{target} 全语料未收 | {label} | {group.Count()} | {Category(label)}");
            }
            checks.True(all.Length == managedAddresses.Count && all.Length > caseNames.Count && runtime.Length > 0, target + " 全部托管映射函数有调用审计");
            var selected = audit.RootElement.EnumerateArray().Where(a => caseNames.Contains(a.GetProperty("cpp_name").GetString()!)).ToArray();
            checks.True(selected.Select(a => a.GetProperty("cpp_name").GetString()).Distinct().Count() == caseNames.Count, target + " 覆盖全部用例的调用审计");
            var runtimeCalls = 0;
            var coveredCalls = 0;
            var runtimeTargets = new HashSet<string>(StringComparer.Ordinal);
            var coveredTargets = new HashSet<string>(StringComparer.Ordinal);
            var missing = new SortedDictionary<string, string>(StringComparer.Ordinal);
            var unclassified = new SortedSet<string>(StringComparer.Ordinal);
            foreach (var call in selected.SelectMany(a => a.GetProperty("direct_calls").EnumerateArray()))
            {
                var names = call.GetProperty("names").EnumerateArray().Select(n => n.GetString()!).ToArray();
                var known = names.Any(mangled.Contains);
                var runtimeNames = names.Where(n => mangled.Contains(n) || IsRuntime(n, symbols)).ToArray();
                if (runtimeNames.Length == 0)
                {
                    foreach (var name in names)
                        if (!symbols.TryGetValue(name, out var symbol) || symbol.GetProperty("cpp_name").ValueKind == JsonValueKind.Null)
                            unclassified.Add(name);
                    continue;
                }
                runtimeCalls++;
                var identity = call.GetProperty("target").GetString()!;
                runtimeTargets.Add(identity);
                if (known) { coveredCalls++; coveredTargets.Add(identity); }
                else foreach (var name in runtimeNames) missing[name] = Reason(name, symbols);
            }
            Console.WriteLine($"{target}：符号 {present}/{catalog.Functions.Length}；用例 {selected.Length}/{caseNames.Count}；运行时直接调用点 {coveredCalls}/{runtimeCalls}；不同目标 {coveredTargets.Count}/{runtimeTargets.Count}");
            foreach (var (name, reason) in missing) Console.WriteLine($"{target} 未覆盖 {name}：{reason}");
            foreach (var name in unclassified) Console.WriteLine($"{target} 待分类直接目标 {name}：未计入运行时分母，须人工确认");
            checks.True(unclassified.Count == 0, target + " 直接目标没有未分类项");
            checks.True(runtimeCalls > 0 && coveredCalls > 0, target + " 真实直接调用覆盖非空");
        }
        return checks.Finish("运行时目录真值核对（缺项逐项报告，不假定全部存在）");
    }
    // 分类仅服务覆盖报告，不用于目录识别或恢复。
    private static string Category(string name)
    {
        var n = name.ToLowerInvariant();
        if (n.Contains(" / ") && !name.Split(" / ", StringSplitOptions.None).All(a => a.Contains("icall", StringComparison.OrdinalIgnoreCase))) return "其他";
        if (n.Contains("write_instance_field_data") || n.Contains("writebarrier") || n.Contains("field_data_pointer") || n.Contains("thread_static_data")) return "其他";
        if (n.Contains("unbox")) return "类型";
        if (n.Contains("constrained_call")) return "泛型";
        if (n.Contains("terminate")) return "异常";
        if (n.Contains("icall")) return "内部调用";
        if (n.Contains("marshal") || n.Contains("pinvoke") || n.Contains("cominterface") || n.Contains("rcw")) return "互操作";
        if (n.Contains("exception") || n.Contains("throw") || n.Contains("cxa_") || n.Contains("unwind")) return "异常";
        if (n.Contains("rgctx") || n.Contains("generic")) return "泛型";
        if (n.Contains("alloc") || n.Contains("new") || n.Contains("box")) return "分配";
        if (n.Contains("class") || n.Contains("type") || n.Contains("isinst") || n.Contains("cast")) return "类型";
        if (!n.Contains("il2cpp") && (n.StartsWith("std::", StringComparison.Ordinal) || !n.Contains('('))) return "系统库";
        return "其他";
    }
    private static string Demangled(string name, Dictionary<string, JsonElement> symbols) => symbols.TryGetValue(name, out var f)
        ? f.GetProperty("demangled_name").GetString() ?? name : name;
    private static bool IsRuntime(string name, Dictionary<string, JsonElement> symbols)
    {
        var n = Demangled(name, symbols);
        return n.StartsWith("il2cpp", StringComparison.Ordinal) || n.StartsWith("Il2Cpp", StringComparison.Ordinal) ||
            n.StartsWith("__cxa_", StringComparison.Ordinal) || n.StartsWith("_Unwind_", StringComparison.Ordinal) ||
            n.StartsWith("__stack_chk_", StringComparison.Ordinal) || new[] { "memcpy", "memmove", "memset", "malloc", "free", "abort" }.Contains(n) || n.Contains("terminate", StringComparison.Ordinal) ||
            new[] { "IsInst(", "Castclass(", "RaiseInvalidCastException(", "Box(", "UnBox", "SZArrayNew(", "GenArrayNew(", "NullCheck(", "InitializedTypeInfo(", "GetVirtualMethodInfo(", "GetInterfaceMethodInfo(" }.Any(p => n.StartsWith(p, StringComparison.Ordinal));
    }
    private static string Reason(string name, Dictionary<string, JsonElement> symbols)
    {
        var n = Demangled(name, symbols);
        if (n.StartsWith("__cxa_", StringComparison.Ordinal)) return "C++ 异常 ABI 的分配、捕获或抛出接口；属于目标异常模型，无对应 libil2cpp 头文件声明";
        if (n.StartsWith("_Unwind_", StringComparison.Ordinal)) return "系统展开器；登记了继续展开语义，目录待匹配目标系统头文件";
        if (n.StartsWith("__stack_chk_", StringComparison.Ordinal) || new[] { "memcpy", "memmove", "memset", "malloc", "free", "abort" }.Contains(n)) return "系统栈保护失败入口；登记了终止语义，目录待匹配目标系统头文件";
        if (n.Contains("terminate", StringComparison.Ordinal)) return "C++ 展开终止入口；目录待目标 C++ ABI 声明";
        if (n.Contains("get_", StringComparison.Ordinal) && n.Contains("exception", StringComparison.Ordinal)) return "异常对象工厂；不能当成抛出，异常对象构造不在本次目录范围";
        return "运行时入口：" + n + "；现有选定头文件尚无经实现核对的映射，保留目录缺口";
    }
}
