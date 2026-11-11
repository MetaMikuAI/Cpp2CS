using Cpp2CS.Input;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Runtime.Layouts;
using Cpp2CS.Targets.Arm64.Abi;
using Cpp2CS.Targets.Elf;

namespace Cpp2CS.Tests;

internal static class BindingCorpusChecks
{
    public const string Command = "binding-corpus";
    public static int Run()
    {
        var root = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        if (string.IsNullOrEmpty(root)) { Console.WriteLine("跳过绑定语料：未设置 CPP2CS_CORPUS。"); return 0; }
        var image = ElfImage.Load(Path.Combine(root, "artifacts/il2cppOutput/build/arm64-v8a/libil2cpp.so"));
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var (model, registration) = ModelBuilder.Load(image, Path.Combine(root, "artifacts/il2cppOutput/data/Metadata/global-metadata.dat"), spec);
        var (map, problems) = RegistrationReader.Read(image, model, spec, registration.CodeRegistration, registration.MetadataRegistration);
        foreach (var problem in problems) Console.WriteLine("代码地图诊断：" + problem);
        var binder = new MethodBinder(new(new FieldLayouts(spec, image.PointerWidth, image.PointerWidth)), new Aapcs64());
        var results = map.Entries.Select(entry => (Entry: entry, Binding: binder.Entry(Project(entry)))).ToArray();
        var a = new Assertions();
        var validReasons = results.All(r => r.Binding.Success || r.Binding.Failure is { Detail.Length: > 0 });
        Console.WriteLine($"绑定语料入口：总数 {results.Length}，成功 {results.Count(r => r.Binding.Success)}，失败 {results.Count(r => !r.Binding.Success)}");
        foreach (var group in results.Where(r => !r.Binding.Success).GroupBy(r => r.Binding.Failure!.Kind).OrderByDescending(g => g.Count()))
            Console.WriteLine($"失败种类 {group.Key}：{group.Count()}");
        foreach (var group in results.Where(r => !r.Binding.Success).GroupBy(r => r.Binding.Failure!.Detail).OrderByDescending(g => g.Count()))
            Console.WriteLine($"失败原因 {group.Count()}：{group.Key}");
        Console.WriteLine($"多候选地址：{map.ByAddress.Count(p => p.Value.Length > 1)}（逐入口统计不任选候选）");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(truth)) Console.WriteLine("跳过用例清单：未设置 CPP2CS_CORPUS_TRUTH。");
        else
        {
            using var cases = InputCorpusChecks.Json(truth, "cases.json");
            var successes = 0; var total = 0;
            foreach (var item in cases.RootElement.EnumerateArray())
            {
                total++;
                var id = item.GetProperty("mapping").GetProperty("metadata_method_id").GetString();
                var addresses = item.GetProperty("mapping").GetProperty("targets").GetProperty("arm64-v8a")
                    .EnumerateArray().Select(t => InputCorpusChecks.Hex(t.GetProperty("address"))).ToHashSet();
                // 用例真值指向方法本体；同一方法另有的反射调用器已计入全入口统计。
                var entries = results.Where(r => addresses.Contains(r.Entry.Address)
                    && r.Entry.Method is { } method && InputCorpusChecks.Id(method.Method) == id).ToArray();
                var success = entries.Length > 0 && entries.All(r => r.Binding.Success);
                if (success) successes++;
                var detail = entries.Length == 0 ? "EntryNotMapped：入口不在代码地图中" : string.Join("；", entries.Select(r => r.Binding.Success
                    ? $"{r.Entry.Kind} 成功" : $"{r.Entry.Kind} {r.Binding.Failure!.Kind}：{r.Binding.Failure.Detail}"));
                Console.WriteLine($"用例 {item.GetProperty("case").GetProperty("method").GetString()}：{detail}");
            }
            Console.WriteLine($"用例合计：{successes}/{total} 成功");
        }
        a.True(validReasons, "全部入口绑定未抛出异常，失败都有原因");
        return a.Finish("绑定语料");
    }

    // 此适配属于装配边界；Recovery 不引用 Input，也不依赖注册表的格式。
    internal static BindingEntry Project(CodeEntry entry) => new(entry.Method, entry.Kind switch
    {
        EntryKind.Method => BindingEntryKind.Ordinary,
        EntryKind.GenericMethod or EntryKind.GenericAdjustorThunk => BindingEntryKind.SharedGeneric,
        EntryKind.AdjustorThunk => BindingEntryKind.AdjustorThunk,
        EntryKind.Invoker => BindingEntryKind.Invoker,
        _ => BindingEntryKind.Wrapper,
    }, entry.Kind.ToString());
}
