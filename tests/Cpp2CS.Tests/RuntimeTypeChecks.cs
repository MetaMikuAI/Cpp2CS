using System.Text.Json;
using Cpp2CS.Native;

public static class RuntimeTypeChecks
{
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
        session.Save(result, "artifacts/runtime-types");
    }
}
