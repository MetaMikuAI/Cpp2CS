using System.Diagnostics;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Elf;
namespace Cpp2CS.Tests;

internal static class FieldLayoutCorpusChecks
{
    public const string Command = "field-layout-corpus";
    /// <summary>没有依据的差异数；有依据的三类分别计数，不算在内。</summary>
    internal static int Differences;
    /// <summary>
    /// 重算与元数据不同而有依据的三类：模块伪类型没有实例；运行时自己定义布局的类型带有元数据里没有的原生成员；
    /// 含显式布局值类型字段的非泛型类型，生成器与运行时算法对该字段的对齐结论不同，运行时对非泛型类型读元数据。
    /// names 为假时不输出类型的名字。
    /// </summary>
    internal static string Compare(ProgramModel model, RuntimeSpec spec, bool names = true)
    {
        var layouts = new FieldLayouts(spec, 8, 8);
        var same = 0; var different = 0; var unavailable = 0;
        var categories = new Dictionary<string, int>();
        var rows = new List<string>();
        foreach (var d in model.Types.Where(t => t.GenericParameters.Count == 0))
        {
            var layout = layouts.Compute(new DefinitionRef(d, []));
            if (layout is null || d.Size <= 0) { unavailable++; if (names) Console.WriteLine($"布局缺数据：{d.FullName}"); continue; }
            var reasons = new List<string>();
            var expected = d.Size + (d.IsValueType ? layout.ObjectHeaderSize : 0);
            if (layout.InstanceSize != expected) reasons.Add($"实例大小 {layout.InstanceSize}/{expected}");
            foreach (var f in layout.Fields.Concat(layout.Statics))
            {
                if (f.Field.Offset < 0) { reasons.Add("字段偏移缺失"); continue; }
                var offset = f.Field.Offset + (d.IsValueType && !f.Field.IsStatic ? layout.ObjectHeaderSize : 0);
                if (f.Offset != offset) reasons.Add($"字段 {f.Field.Name} {f.Offset}/{offset}");
            }
            rows.Add($"{d.Assembly}:{d.Token}:{layout.InstanceSize}:{string.Join(',', layout.Fields.Concat(layout.Statics).Select(f => f.Offset))}");
            if (reasons.Count == 0) same++;
            else
            {
                different++;
                var category = d.Name == "<Module>" ? "模块伪类型" : d.FullName is "System.Array" or "System.__Il2CppComObject" or "System.__Il2CppComDelegate" or "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericType" or "Unity.IL2CPP.Metadata.__Il2CppFullySharedGenericStructType" ? "运行时定义大小" : d.Fields.Any(f => f.Type is DefinitionRef { Definition.Attributes: var attr } && (attr & System.Reflection.TypeAttributes.LayoutMask) == System.Reflection.TypeAttributes.ExplicitLayout)
                    ? "含显式值类型" : "其他";
                categories[category] = categories.GetValueOrDefault(category) + 1;
                Console.WriteLine($"布局差异 {category} {(names ? d.FullName : "0x" + d.Token.ToString("x8"))}：{(names ? string.Join("；", reasons) : reasons.Count + " 处")}");
            }
        }
        Console.WriteLine($"非泛型：一致 {same}，不一致 {different}，缺数据 {unavailable}；{string.Join(',', categories.Select(p => p.Key + "=" + p.Value))}");
        Differences = categories.GetValueOrDefault("其他");
        return string.Join('\n', rows.Order(StringComparer.Ordinal));
    }
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过字段布局语料：未设置 CPP2CS_CORPUS。"); return 0; }
        var a = new Assertions(); string? previous = null;
        var evidencePath = Path.Combine(Path.GetTempPath(), "cpp2cs-field-layout-" + Guid.NewGuid() + ".local.json");
        var start = new ProcessStartInfo("python3") { UseShellExecute = false };
        start.ArgumentList.Add(Path.Combine("corpus", "truth", "field-layouts.py"));
        start.ArgumentList.Add(root); start.ArgumentList.Add(evidencePath);
        using (var process = Process.Start(start)!) { process.WaitForExit(); if (process.ExitCode != 0) return 1; }
        using var evidence = JsonDocument.Parse(File.ReadAllBytes(evidencePath));
        File.Delete(evidencePath);
        foreach (var target in new[] { "arm64-v8a", "x86_64" })
        {
            var timer = Stopwatch.StartNew();
            var image = ElfImage.Load(Path.Combine(root, "artifacts/il2cppOutput/build", target, "libil2cpp.so"));
            var spec = InputCorpusChecks.Spec(target);
            var (model, _) = ModelBuilder.Load(image, Path.Combine(root, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
            var current = Compare(model, spec);
            a.True(Differences == 0, "非泛型重算与元数据的差异都属于有依据的三类");
            var layouts = new FieldLayouts(spec, image.PointerWidth, image.PointerWidth);
            Console.WriteLine($"模型中封闭泛型值类型的非默认打包实例：{model.RuntimeTypes.OfType<DefinitionRef>().Where(t => t.Definition.IsValueType && t.Arguments.Count > 0 && !t.ContainsGenericParameter() && t.Definition.PackingSize > 0).Distinct().Count()}");
            var count = 0; var nested = 0; var references = 0; var wide = 0; var packed = 0;
            var seen = new HashSet<DefinitionRef>();
            foreach (var entry in evidence.RootElement.EnumerateArray())
            {
                if (model.RuntimeTypes[entry.GetProperty("index").GetInt32()] is not DefinitionRef { Definition.IsValueType: true, Arguments.Count: > 0 } type
                    || type.ContainsGenericParameter() || !seen.Add(type)) continue;
                var layout = layouts.Of(type);
                if (layout is null) { a.True(false, "泛型缺布局：" + type); continue; }
                var offsets = entry.GetProperty("offsets").EnumerateArray().Select(e => e.GetInt32()).ToArray();
                a.True(layout.ValueSize == entry.GetProperty("size").GetInt32() && layout.Fields.Select(f => f.Offset - layout.ObjectHeaderSize).SequenceEqual(offsets), "C++ 泛型大小与字段次序/偏移：" + type);
                count++;
                if (layout.HasReferences) references++;
                if (layout.Fields.Any(f => f.Type is DefinitionRef { Definition.IsValueType: true } d && ManagedTypes.PrimitiveName(d) is null)) nested++;
                if (layout.Fields.Any(f => layouts.SizeAndAlignment(f.Type).Alignment == 8)) wide++;
                if (type.Definition.PackingSize > 0) packed++;
            }
            Console.WriteLine($"泛型 C++ 对照 {count}；嵌套 {nested}，含引用 {references}，8 字节对齐成员 {wide}，打包 {packed}");
            // 语料里没有带打包的封闭泛型值类型，这一类没有对照。
            a.True(count >= 30 && nested > 0 && references > 0 && wide > 0, "泛型对照数量和覆盖");
            a.True(previous is null || previous == current, "两个目标布局相同"); previous = current;
            Console.WriteLine($"{target}：{timer.Elapsed.TotalSeconds:F2}s");
        }
        return a.Finish("字段布局语料");
    }
}

internal static class FieldLayoutSampleChecks
{
    public const string Command = "field-layout-sample";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_SAMPLES");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过字段布局样本：未设置 CPP2CS_SAMPLES。"); return 0; }
        using var manifest = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(root, "manifest.json")));
        var group = manifest.RootElement.GetProperty("groups").EnumerateObject().First(g =>
            g.Value.GetProperty("files").EnumerateArray().Any(f => f.TryGetProperty("binary", out var b) && b.GetProperty("format").GetString() == "ELF") &&
            g.Value.GetProperty("files").EnumerateArray().Any(f => f.TryGetProperty("metadata", out var m) && m.GetProperty("version_int32").GetInt32() == 31));
        var files = group.Value.GetProperty("files").EnumerateArray().ToArray();
        string Local(JsonElement f) => Path.Combine(root, group.Name, f.GetProperty("copy").GetString()!.Replace('\\', '/').Split('/')[^1]);
        var timer = Stopwatch.StartNew();
        var image = ElfImage.Load(Local(files.Single(f => f.TryGetProperty("binary", out _))));
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, _) = ModelBuilder.Load(image, Local(files.Single(f => f.TryGetProperty("metadata", out _))), spec);
        FieldLayoutCorpusChecks.Compare(model, spec, names: false);
        Console.WriteLine($"主样本：耗时 {timer.Elapsed.TotalSeconds:F2}s，峰值工作集 {Process.GetCurrentProcess().PeakWorkingSet64 / 1024d / 1024:F1} MiB");
        return FieldLayoutCorpusChecks.Differences == 0 ? 0 : 1;
    }
}
