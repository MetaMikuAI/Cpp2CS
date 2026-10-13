using System.Text.Json;
using Cpp2CS.Native;

public static class NamespaceCorpusChecks
{
    public static void Run(Action<bool, string> check)
    {
        const string directory = "artifacts/corpus-inventory-check";
        Directory.CreateDirectory(directory);
        var assembly = typeof(NamespaceCorpusChecks).Assembly.Location;
        var symbols = Path.Combine(directory, "script.json");
        File.WriteAllText(symbols, """{"ScriptMethod":[{"Address":256,"Name":"CorpusFixture.Root$$Run"},{"Address":512,"Name":"CorpusFixture.Generic<int>$$Run"}]}""");
        var config = Path.Combine(directory, "inputs.json");
        File.WriteAllText(config, JsonSerializer.Serialize(new NativeInputs(assembly, symbols, assembly, assembly, "unused", "unused")));
        var manifest = Path.Combine(directory, "manifest.json");
        NamespaceCorpus.Inventory(config, manifest, ["CorpusFixture"]);
        using var document = JsonDocument.Parse(File.ReadAllText(manifest));
        var methods = document.RootElement.GetProperty("methods").EnumerateArray().ToArray();
        check(methods.Length == 5, "清单包含目标空间的普通、重载、嵌套、抽象和子空间方法，排除相似前缀");
        check(methods.Count(m => m.GetProperty("address").ValueKind == JsonValueKind.Null) == 4, "没有 VA 的定义仍保留在完整清单");
        check(methods.Single(m => m.GetProperty("address").ValueKind != JsonValueKind.Null).GetProperty("address").GetUInt64() == 256,
            "原生地址来自 AddressAttribute，不从 DummyDLL 方法体 RVA 推断");
        check(methods.Select(m => m.GetProperty("id").GetString()).Distinct().Count() == 5, "重载按程序集与定义 Token 区分");
        check(document.RootElement.GetProperty("additionalSymbols").GetArrayLength() == 1, "只有原生符号的泛型实例单独保留");
    }
}

namespace CorpusFixture
{
    public static class Root
    {
        [Il2CppDummyDll.Address(VA = "0x100")]
        public static void Run() { }
        public static void Run(int value) { }
        public static class Nested { public static void Run() { } }
    }
    public interface IContract { void Run(); }
}
namespace CorpusFixture.Child { public static class Root { public static void Run() { } } }
namespace CorpusFixtureOther { public static class Root { public static void Run() { } } }
namespace Il2CppDummyDll
{
    [AttributeUsage(AttributeTargets.Method)]
    public sealed class AddressAttribute : Attribute { public string? VA; }
}
