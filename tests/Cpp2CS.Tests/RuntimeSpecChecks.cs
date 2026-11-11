using System.Numerics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using Cpp2CS.Runtime;

namespace Cpp2CS.Tests;

internal static class RuntimeSpecChecks
{
    public const string Command = "runtime";

    public static int Run()
    {
        var checks = new Assertions();
        foreach (var path in Directory.EnumerateFiles(Path.Combine(ArchitectureChecks.FindRoot(), "spec"), "unity-*.json"))
        {
            using var doc = JsonDocument.Parse(File.ReadAllText(path));
            var root = doc.RootElement;
            var version = root.GetProperty("unity_version").GetString()!;
            var targets = root.TryGetProperty("targets", out var ts) ? ts.EnumerateArray().ToArray() : [root.GetProperty("target")];
            foreach (var target in targets)
            {
                var triple = target.GetProperty("triple").GetString()!;
                var model = target.GetProperty("data_model").GetString()!;
                var layout = RuntimeSpec.Load(path, version, triple, model).Layout;
                var embedded = RuntimeSpec.Select(version, triple, model).Layout;
                foreach (var record in root.GetProperty("records").EnumerateObject())
                {
                    var actual = layout.Record(record.Name);
                    checks.True(actual.Size == record.Value.GetProperty("size").GetInt64() &&
                        actual.Alignment == record.Value.GetProperty("alignment").GetInt64() &&
                        actual.Type == record.Value.GetProperty("type").GetString() &&
                        actual.Kind == record.Value.GetProperty("kind").GetString(), $"{record.Name} 大小、对齐与类型");
                    checks.True(embedded.Record(record.Name).Size == actual.Size, "嵌入数据与文件一致");
                    Fields(checks, record.Value.GetProperty("fields"), actual.Field);
                    Fields(checks, record.Value.GetProperty("fields"), embedded.Record(record.Name).Field);
                }
                foreach (var constant in root.GetProperty("constants").EnumerateObject())
                    checks.True(layout.Constant(constant.Name) == BigInteger.Parse(constant.Value.GetRawText()), $"常量 {constant.Name}");
                foreach (var primitive in target.GetProperty("primitives").EnumerateObject())
                    checks.True(layout.Primitive(primitive.Name).Size == primitive.Value.GetProperty("size").GetInt64() &&
                        layout.Primitive(primitive.Name).Alignment == primitive.Value.GetProperty("alignment").GetInt64(), $"基本类型 {primitive.Name}");
                checks.True(layout.ObjectHeaderSize == layout.Record("Il2CppObject").Size, "对象头定义");
                checks.True(layout.ArrayDataStart == layout.Field("Il2CppArraySize", "vector").ByteOffset, "数组数据定义");
                checks.True(layout.StringCharactersStart == layout.Field("Il2CppString", "chars").ByteOffset &&
                    layout.StringCharactersStart != layout.Record("Il2CppString").Size, "字符区不能用 sizeof 代替");
                checks.True(layout.VtableStart == layout.Field("Il2CppClass", "vtable").ByteOffset &&
                    layout.VtableSlotSize == layout.Record("VirtualInvokeData").Size, "虚表定义");
                foreach (var slot in new long[] { 0, 1, 7 })
                    foreach (var field in new[] { layout.VirtualCallMethodPointer, layout.VirtualCallMethodInfo })
                        checks.True(layout.VtableSlotFieldOffset(slot, field.Path.Split('.')[^1]) ==
                            layout.VtableStart + slot * layout.VtableSlotSize + field.ByteOffset, "虚表槽字段定义");
                Reject<KeyNotFoundException>(checks, () => layout.Record("missing"), path, "missing");
                Reject<KeyNotFoundException>(checks, () => layout.Field("Il2CppObject", "missing"), path, "Il2CppObject.missing");
                Reject<KeyNotFoundException>(checks, () => layout.Field("Il2CppObject", "klass").Member("missing"), path, "klass.missing");
                Reject<KeyNotFoundException>(checks, () => layout.Constant("missing"), path, "missing");
                Reject<KeyNotFoundException>(checks, () => layout.Primitive("missing"), path, "missing");
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Load(path, "missing", triple, model), path, "missing");
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Load(path, version, "missing", model), path, "missing");
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Load(path, version, triple, "missing"), path, "missing");
                Reject<ArgumentOutOfRangeException>(checks, () => layout.VtableSlotFieldOffset(-1, "method"));
                Reject<OverflowException>(checks, () => layout.VtableSlotFieldOffset(long.MaxValue, "method"));
                var changed = JsonNode.Parse(root.GetRawText())!;
                changed["schema_version"] = int.MaxValue;
                using var stream = new MemoryStream(Encoding.UTF8.GetBytes(changed.ToJsonString()));
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Read(stream, "unknown.json", version, triple, model), "unknown.json", "schema_version");
                changed["schema_version"] = "unsupported";
                using var textVersion = new MemoryStream(Encoding.UTF8.GetBytes(changed.ToJsonString()));
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Read(textVersion, "unknown.json", version, triple, model), "unknown.json", "schema_version");
                changed.AsObject().Remove("schema_version");
                using var absentVersion = new MemoryStream(Encoding.UTF8.GetBytes(changed.ToJsonString()));
                Reject<InvalidDataException>(checks, () => RuntimeSpec.Read(absentVersion, "unknown.json", version, triple, model), "unknown.json", "schema_version");
                var results = Enumerable.Range(0, 64).AsParallel().Select(_ => layout.Record("Il2CppObject")).ToArray();
                checks.True(results.All(r => ReferenceEquals(r, results[0])), "并发查询共享不可变记录");
            }
        }
        Reject<InvalidDataException>(checks, () => RuntimeSpec.Select("missing", "missing", "missing"), "嵌入布局", "missing");
        return checks.Finish("运行时规格");
    }

    private static void Fields(Assertions checks, JsonElement fields, Func<string, RuntimeField> query)
    {
        foreach (var expected in fields.EnumerateArray())
        {
            var actual = query(expected.GetProperty("name").GetString()!);
            var bits = expected.GetProperty("offset_bits").GetInt64();
            checks.True(actual.OffsetBits == bits && actual.Size == expected.GetProperty("size").GetInt64() &&
                actual.Type == expected.GetProperty("type").GetString(), actual.Path);
            if (expected.TryGetProperty("bit_width", out var width))
            {
                var storage = actual.BitStorage;
                checks.True(storage.ByteOffset * 8 + storage.BitOffset == bits && storage.BitWidth == width.GetInt64() &&
                    storage.ByteSize == (storage.BitOffset + width.GetInt64() + 7) / 8, $"{actual.Path} 位域");
                Reject<InvalidOperationException>(checks, () => actual.ByteOffset, actual.Path);
            }
            else
            {
                checks.True(actual.ByteOffset * 8 == bits && actual.BitWidth is null, $"{actual.Path} 字节偏移");
                Reject<InvalidOperationException>(checks, () => actual.BitStorage, actual.Path);
            }
            if (expected.TryGetProperty("members", out var members)) Fields(checks, members, actual.Member);
        }
    }

    // 仅测试预期失败，不在产品逻辑中吞异常。
    private static void Reject<T>(Assertions checks, Func<object> action, params string[] fragments) where T : Exception
    {
        try { action(); checks.True(false, $"应抛出 {typeof(T).Name}"); }
        catch (T error) { checks.True(fragments.All(f => error.Message.Contains(f, StringComparison.Ordinal)), error.Message); }
    }
}
