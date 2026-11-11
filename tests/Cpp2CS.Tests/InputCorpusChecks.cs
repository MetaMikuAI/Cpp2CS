using System.Diagnostics;
using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Runtime;
using Cpp2CS.Targets.Elf;
using Cpp2CS.Native.Images;
namespace Cpp2CS.Tests;

internal static class InputCorpusChecks
{
    public const string Command = "input-corpus";
    internal static RuntimeSpec Spec(string target) => RuntimeSpec.Select("2022.3.62f2", target == "arm64-v8a" ? "aarch64-linux-android" : "x86_64-linux-android", "LP64");
    internal static string Id(MethodDef m) => $"{m.Owner.Assembly}:0x{m.Token:x8}";
    internal static string TypeName(TypeDef t) => t.DeclaringType is { } d ? TypeName(d) + "/" + t.Name : (t.Namespace.Length == 0 ? "" : t.Namespace + ".") + t.Name;
    internal static string TypeText(TypeRef t) => t switch
    {
        DefinitionRef d => TypeName(d.Definition) + (d.Arguments.Count == 0 ? "" : "<" + string.Join(",", d.Arguments.Select(TypeText)) + ">"),
        GenericParameterRef g => g.Name,
        ArrayRef a => TypeText(a.Element) + "[" + (a.Rank == 1 && !a.IsVector ? "*" : new string(',', a.Rank - 1)) + "]",
        ByRefRef b => TypeText(b.Element) + "&",
        PointerRef p => TypeText(p.Element) + "*",
        PrimitiveRef p => p.Name,
        _ => throw new NotSupportedException(t.ToString())
    };
    internal static string Signature(MethodDef m) => $"{TypeText(m.ReturnType)} {TypeName(m.Owner)}::{m.Name}({string.Join(",", m.Parameters.Select(p => TypeText(p.Type)))})";
    internal static bool HasBody(MethodDef m) => !m.IsAbstract && (m.Attributes & MethodAttributes.PinvokeImpl) == 0 &&
        (m.ImplAttributes & (MethodImplAttributes.InternalCall | MethodImplAttributes.Runtime | MethodImplAttributes.Native)) == 0;
    internal static ulong Hex(JsonElement e) => Convert.ToUInt64(e.GetString()![2..], 16);
    internal static JsonDocument Json(string root, string name) => JsonDocument.Parse(File.ReadAllBytes(Path.Combine(root, name)));
    private static string Fingerprint(ProgramModel model)
    {
        string Value(object? value) => value switch
        {
            null => "null", float f => "f32:" + BitConverter.SingleToInt32Bits(f).ToString("X8"), double d => "f64:" + BitConverter.DoubleToInt64Bits(d).ToString("X16"),
            TypeRef t => TypeText(t), AttributeValue[] array => string.Join(";", array.Select(v => TypeText(v.Type) + "=" + Value(v.Value))),
            _ => JsonSerializer.Serialize(value, value.GetType())
        };
        string Attributes(IReadOnlyList<CustomAttributeDef> attrs) => string.Join("|", attrs.Select(a =>
            Id(a.Constructor) + ":" + string.Join(";", a.Arguments.Select(v => TypeText(v.Type) + "=" + Value(v.Value))) + ":" +
            string.Join(";", a.Fields.Select(f => f.Field.Token + "=" + Value(f.Value.Value))) + ":" +
            string.Join(";", a.Properties.Select(p => p.Property.Token + "=" + Value(p.Value.Value)))).Order(StringComparer.Ordinal));
        string Generics(IReadOnlyList<GenericParameterDef> gs) => string.Join("|", gs.OrderBy(g => g.Position).Select(g =>
            $"{g.Position}:{g.Name}:{(int)g.Attributes}:{string.Join(';', g.Constraints.Select(TypeText).Order(StringComparer.Ordinal))}"));
        string Method(MethodRef? m) => m is null ? "null" : $"{Id(m.Method)}<{string.Join(';', m.TypeArguments.Select(TypeText))}>({string.Join(';', m.MethodArguments.Select(TypeText))})";
        var rows = new List<string> { "V|" + model.MetadataVersion };
        rows.AddRange(model.Assemblies.Select(a => $"A|{a.Name}|{a.AssemblyName}|{a.Version}|{a.Culture}|{Convert.ToHexString(a.PublicKey)}|{Attributes(a.CustomAttributes)}"));
        foreach (var t in model.Types)
        {
            var key = $"{t.Assembly}|{TypeName(t)}|{t.Token}";
            rows.Add($"T|{key}|{(int)t.Attributes}|{t.Size}|{t.PackingSize}|{t.ClassSizeIsDefault}|{t.IsValueType}|{t.IsEnum}|{Value(t.BaseType)}|{Generics(t.GenericParameters)}|{Attributes(t.CustomAttributes)}");
            rows.AddRange(t.Interfaces.Select(i => $"I|{key}|{TypeText(i)}"));
            rows.AddRange(t.InterfaceOffsets.Select(i => $"O|{key}|{TypeText(i.Interface)}|{i.Offset}"));
            rows.AddRange(t.VTable.Select((m, i) => $"V|{key}|{i}|{Method(m)}"));
            rows.AddRange(t.Properties.Select(p => $"P|{key}|{p.Token}|{p.Name}|{(int)p.Attributes}|{p.Getter?.Token}|{p.Setter?.Token}|{Attributes(p.CustomAttributes)}"));
            rows.AddRange(t.Events.Select(e => $"E|{key}|{e.Token}|{e.Name}|{TypeText(e.Type)}|{(int)e.Attributes}|{e.Add?.Token}|{e.Remove?.Token}|{e.Raise?.Token}|{Attributes(e.CustomAttributes)}"));
        }
        rows.AddRange(model.Methods.Select(m => $"M|{Id(m)}|{Signature(m)}|{(int)m.Attributes}|{(int)m.ImplAttributes}|{m.Slot}|{m.ReturnParameterToken}|{Generics(m.GenericParameters)}|{Attributes(m.CustomAttributes)}|{Attributes(m.ReturnAttributes)}|" +
            string.Join(";", m.Parameters.Select(p => $"{p.Token}:{p.Name}:{TypeText(p.Type)}:{(int)p.Attributes}:{p.HasDefault}:{Value(p.DefaultValue)}:{Attributes(p.CustomAttributes)}"))));
        rows.AddRange(model.Fields.Select(f => $"F|{f.Owner.Assembly}|{TypeName(f.Owner)}|{f.Token}|{f.Name}|{TypeText(f.Type)}|{f.Offset}|{(int)f.Attributes}|{Value(f.Constant)}|{(f.InitialValue is null ? "null" : Convert.ToHexString(f.InitialValue))}|{f.IsThreadStatic}|{Attributes(f.CustomAttributes)}"));
        rows.AddRange(model.MethodSpecs.Select(m => "G|" + Method(m)));
        rows.AddRange(model.RuntimeTypes.Select(t => "R|" + TypeText(t)));
        rows.AddRange(model.FieldRefs.Select(f => $"FR|{TypeText(f.DeclaringType)}|{f.Field.Owner.Assembly}|{f.Field.Token}"));
        rows.AddRange(model.StringLiterals.Select(s => "S|" + JsonSerializer.Serialize(s)));
        return Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(string.Join('\n', rows.Order(StringComparer.Ordinal)))));
    }
    /// <summary>映像里该方法的返回值与各参数类型是否都没有记录自定义修饰符。</summary>
    private static bool ImageHasNoModifiers(IImage image, RuntimeSpec spec, ModelRegistration registration, int index, string metadataPath)
    {
        using var metadata = new Il2CppDumper.Metadata(new MemoryStream(File.ReadAllBytes(metadataPath)));
        var data = new RuntimeData(image, spec);
        var table = data.Pointer(registration.MetadataRegistration, "Il2CppMetadataRegistration", "types");
        var method = metadata.methodDefs[index];
        var indices = new[] { method.returnType }.Concat(Enumerable.Range(method.parameterStart, method.parameterCount).Select(i => metadata.parameterDefs[i].typeIndex));
        var counts = indices.Select(i => (Index: i, Count: data.Number(data.Pointer(table + (ulong)i * (ulong)image.PointerWidth), "Il2CppType", "num_mods"))).ToArray();
        Console.WriteLine("签名修饰符映像证据（返回值、参数）：" + string.Join("，", counts.Select(c => $"type[{c.Index}].num_mods={c.Count}")));
        return counts.All(c => c.Count == 0);
    }
    private static string WithoutModifiers(string signature) =>
        System.Text.RegularExpressions.Regex.Replace(signature, @" mod(req|opt)\([^)]*\)", "");
    public static int Run()
    {
        var corpus = Environment.GetEnvironmentVariable("CPP2CS_CORPUS");
        var truth = Environment.GetEnvironmentVariable("CPP2CS_CORPUS_TRUTH");
        if (string.IsNullOrEmpty(corpus) || string.IsNullOrEmpty(truth)) { Console.WriteLine("跳过 Input 定向检查：未设置 CPP2CS_CORPUS 或 CPP2CS_CORPUS_TRUTH。"); return 0; }
        var a = new Assertions();
        string? digest = null;
        foreach (var target in new[] { "arm64-v8a", "x86_64" })
        {
            var timer = Stopwatch.StartNew();
            var image = ElfImage.Load(Path.Combine(corpus, "artifacts", "il2cppOutput", "build", target, "libil2cpp.so"));
            var spec = Spec(target);
            var (model, builder) = ModelBuilder.Load(image, Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat"), spec);
            var (registrations, problems) = RegistrationReader.Read(image, model, spec, builder.CodeRegistration, builder.MetadataRegistration);
            a.True(problems.Count == 0, "注册表诊断");
            var byId = model.Methods.ToDictionary(Id);
            using var methods = Json(truth, "methods.json");
            var differences = new Dictionary<string, int>();
            void Compare(bool same, string category, string detail)
            {
                if (same) return;
                differences[category] = differences.GetValueOrDefault(category) + 1;
                if (differences[category] <= 3) Console.WriteLine($"{target} {category}：{detail}");
            }

            var truthIds = methods.RootElement.EnumerateArray().Select(m => m.GetProperty("id").GetString()!).ToHashSet();
            using var unmatched = Json(truth, "unmatched-metadata.json");
            var extraEvidence = unmatched.RootElement.EnumerateArray().ToDictionary(m => m.GetProperty("metadata_method_id").GetString()!);
            // 生成器自己加的模块在元数据里有方法而没有托管输入；真值把它们逐个列为“未对应的元数据”。没被真值解释的多余方法算差异。
            var extras = byId.Keys.Except(truthIds).Order(StringComparer.Ordinal).ToArray();
            foreach (var extra in extras)
            {
                var explained = extraEvidence.TryGetValue(extra, out var evidence);
                Console.WriteLine($"{target} 额外元数据方法 {extra}：{(explained ? evidence.GetProperty("reason").GetString() : "真值未解释")}");
                Compare(explained, "多余方法未解释", extra);
            }
            Compare(model.Methods.Count == methods.RootElement.GetArrayLength() + extras.Length, "数量",
                $"模型 {model.Methods.Count}，真值 {methods.RootElement.GetArrayLength()}，多余 {extras.Length}");
            var modifiersNotInImage = 0;
            foreach (var m in methods.RootElement.EnumerateArray())
            {
                var id = m.GetProperty("id").GetString()!;
                if (!byId.TryGetValue(id, out var actual)) { Compare(false, "缺方法或标记", id); continue; }
                Compare(actual.Token == Hex(m.GetProperty("token")), "标记", id);
                Compare(TypeName(actual.Owner) == m.GetProperty("declaring_type").GetString(), "声明类型", id);
                var expected = m.GetProperty("signature").GetString()!;
                var same = Signature(actual) == expected;
                // 真值来自托管程序集，带自定义修饰符；il2cpp 的元数据不保存它们。只差修饰符、并且映像里确实没有记录时单独计数，不算差异。
                if (!same && Signature(actual) == WithoutModifiers(expected) &&
                    ImageHasNoModifiers(image, spec, builder, actual.Index, Path.Combine(corpus, "artifacts", "il2cppOutput", "data", "Metadata", "global-metadata.dat")))
                {
                    modifiersNotInImage++;
                    Console.WriteLine($"{target} 映像不保存的修饰符：{id}：{expected}");
                    same = true;
                }
                Compare(same, "签名", id + "：" + Signature(actual) + " != " + expected);
                Compare(HasBody(actual) == m.GetProperty("has_body").GetBoolean(), "方法体", id);
            }
            Console.WriteLine($"{target} 模型：{model.Methods.Count} 方法，其中生成器模块多出 {extras.Length}；映像不保存修饰符的签名 {modifiersNotInImage}；差异 " + string.Join("，", differences.Select(p => $"{p.Key}={p.Value}")));
            a.True(differences.Count == 0, $"{target} 模型逐方法一致");
            var current = Fingerprint(model);
            a.True(digest is null || digest == current, "双目标模型与次序无关的摘要一致"); digest = current;
            using var functions = Json(truth, $"functions.{target}.json");
            var symbols = functions.RootElement.EnumerateArray().Where(f => f.GetProperty("defined").GetBoolean())
                .Select(f => (f.GetProperty("name").GetString(), Hex(f.GetProperty("address")))).ToHashSet();
            using var mappings = Json(truth, "mappings.json");
            var counts = new Dictionary<string, (int Matched, int Mismatched)>();
            var actualEntries = registrations.Entries.Where(e => e.Method is not null).Select(e => (Id(e.Method!.Method), e.Address, e.Kind)).ToHashSet();
            foreach (var mapping in mappings.RootElement.EnumerateArray())
            {
                var role = mapping.GetProperty("role").GetString()!;
                EntryKind[] kinds = role switch
                {
                    "ordinary" => [EntryKind.Method], "shared_generic" => [EntryKind.GenericMethod],
                    "adjustor_thunk" => [EntryKind.AdjustorThunk, EntryKind.GenericAdjustorThunk], "invoker" => [EntryKind.Invoker], _ => []
                };
                if (kinds.Length == 0) continue;
                foreach (var entry in mapping.GetProperty("targets").GetProperty(target).EnumerateArray())
                {
                    var address = Hex(entry.GetProperty("address"));
                    var id = mapping.GetProperty("metadata_method_id").GetString()!;
                    var ok = kinds.Any(k => actualEntries.Contains((id, address - image.PreferredBase, k))) && symbols.Contains((entry.GetProperty("symbol_name").GetString(), address));
                    if (mapping.TryGetProperty("method_spec_index", out var specIndex))
                    {
                        var instance = model.MethodSpecs[specIndex.GetInt32()];
                        ok &= registrations.At(address - image.PreferredBase).Any(e => kinds.Contains(e.Kind) && e.Method == instance);
                    }
                    var previous = counts.GetValueOrDefault(role);
                    counts[role] = ok ? (previous.Matched + 1, previous.Mismatched) : (previous.Matched, previous.Mismatched + 1);
                    if (!ok && previous.Mismatched < 3) Console.WriteLine($"{target} 入口差异 {role} {id} 0x{address:x}");
                }
            }
            foreach (var (role, count) in counts) { Console.WriteLine($"{target} {role}：对上 {count.Matched}，对不上 {count.Mismatched}"); a.True(count.Mismatched == 0, $"{target} {role} 入口和分类"); }
            using var generic = Json(truth, "generic-instances.json");
            var genericMatched = 0;
            foreach (var item in generic.RootElement.EnumerateArray())
            {
                var index = item.GetProperty("method_spec_index").GetInt32();
                if (index < builder.Instantiations.Length && builder.Instantiations[index] is var instance &&
                    Id(instance.Method.Method) == item.GetProperty("method_id").GetString() &&
                    instance.ClassIndex == item.GetProperty("class_inst_index").GetInt32() && instance.MethodIndex == item.GetProperty("method_inst_index").GetInt32()) genericMatched++;
            }
            Console.WriteLine($"{target} 泛型实例：对上 {genericMatched}，真值 {generic.RootElement.GetArrayLength()}，模型 {model.MethodSpecs.Count}");
            a.True(genericMatched == generic.RootElement.GetArrayLength() && genericMatched == model.MethodSpecs.Count, "泛型实例索引、定义与实例化对应");
            using var cases = Json(truth, "cases.json");
            var caseMatched = 0;
            foreach (var item in cases.RootElement.EnumerateArray())
            {
                var c = item.GetProperty("case");
                var found = model.Methods.Where(m => m.Owner.FullName == c.GetProperty("type").GetString() && m.Name == c.GetProperty("method").GetString()).ToArray();
                if (found.Length == 1 && registrations.Entries.Any(e => e.Method?.Method == found[0] && e.Kind is EntryKind.Method or EntryKind.GenericMethod)) caseMatched++;
            }
            a.True(caseMatched == cases.RootElement.GetArrayLength(), "全部用例按类型、方法名找到并有入口");
            Console.WriteLine($"{target} 用例 {caseMatched}/{cases.RootElement.GetArrayLength()}，注册槽位 {registrations.MetadataUsageSlots.Count}，耗时 {timer.Elapsed.TotalSeconds:F2}s；摘要 {current}");
        }
        return a.Finish("Input 定向检查");
    }
}
