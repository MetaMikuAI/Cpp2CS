using System.Text.Json;
using Cpp2CS.Native;

public static class RuntimeTypeChecks
{
    public static void Run(Action<bool, string> check)
    {
        check(new MetadataReference(0, "ScriptString", "text", "", 0).ValueType == "System_String_o*", "字符串元数据槽按类别提供托管字符串类型");
        check(new MetadataReference(0, "ScriptMetadataMethod", "Method$Example.Run()", "", 0).ValueType == "MethodInfo*", "方法元数据无 Signature 时保留 MethodInfo 内容类型");
        check(new MetadataReference(0, "ScriptMetadata", "Example_TypeInfo", "Example_c*", 0).ValueType == "Example_c*" &&
            new MetadataReference(0, "ScriptMetadata", "Field$Example.Value", "", 0).ValueType == "unknown", "显式元数据类型保持不变，缺少类型的字段槽不能冒充方法信息");
    }
    public static void Native(Action<bool, string> check, string configuration)
    {
        using var session = new RecoverySession(JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!);
        var analysis = session.Analyze(0x520647c);
        var contexts = analysis.Ssa.Values.Where(v => v.Operation == "load")
            .Select(v => (v.Id, Value: analysis.Semantics.Resolve(v.Id))).Where(v => v.Value.Kind == "runtime-context").ToArray();
        check(contexts.Length == 2 && contexts.All(v => v.Value.Name == "System.Collections.Generic.List<string>" &&
            v.Value.Type is not (null or "Il2CppRGCTXData*")),
            "真实 MethodInfo 的声明类型和泛型上下文由共享 SSA 确认");
        var result = session.Recover(analysis.Method.Address);
        check(contexts.All(c => result.Proofs.Any(p => p.Rule == "SharedSsaRuntimeType" && p.Detail.StartsWith(c.Id + ":"))),
            "回退投影消费同一读取身份的类型证据，不重新识别机器指令");
        check(result.Problems.All(p => !p.Contains("load(MethodInfo*+0x20)") && !p.Contains("load(Il2CppRGCTXData*+0x70)")),
            "已绑定上下文的后续方法槽读取不退化成未知 union 访问");
        var strings = analysis.Ssa.Values.Select(v => analysis.Semantics.Resolve(v.Id))
            .Where(v => v.Kind == "metadata" && session.Symbols.Metadata.GetValueOrDefault(unchecked((ulong)v.Offset))?.Kind == "ScriptString").ToArray();
        check(strings.Length > 0 && strings.All(v => v.Type == "System_String_o*"), "真实字符串槽的 SSA 内容类型与原生字符串返回类型一致");
        check(result.Problems.Count == 0 && result.Blocks.Values.SelectMany(b => b.Statements).OfType<DeclareStatement>().Any(d => d.Type == "System_String_o*"),
            "真实字符串字面量与字符串调用结果的 Phi 保留引用类型，已知入口无剩余报告缺口");
        session.Save(result, "artifacts/runtime-types");
    }
}
