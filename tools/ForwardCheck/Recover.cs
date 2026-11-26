using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 恢复的主线（设计第 9、10 节）在语料上的运行与 IL 对照（第 15 节）：
/// 快照 → 效果图 → 发现 → 证明 → 选择 → 下降 → 托管方法体；恢复出的 IL 与真实 IL 都按目录展开，由同一个引擎证明等价。
/// 恢复过程只读快照、签名与全局事实，不读真实 IL；真实 IL 只用于对照。
/// </summary>
internal static partial class Recover
{
    public static int Run(string casesPath, string assemblies, string binary, string metadataPath, string symbolFile, string target, string show)
    {
        using var document = JsonDocument.Parse(File.ReadAllBytes(casesPath));
        var input = Il2CppInput.Load(binary, metadataPath);
        byte[] bytes = File.ReadAllBytes(binary);
        using var metadata = ModelInput.Open(assemblies, input, bytes);
        var facts = new BridgeFacts(input, metadata.Facts, symbolFile, bytes);
        var entities = new EntityFacts(metadata.Facts);
        var lifter = new Arm64Target(input.Elf, bytes,
            input.Code.Methods.Concat(input.Code.MethodInstances).Where(m => m.Entry.HasValue).Select(m => m.Entry!.Value));
        var lifts = new Dictionary<ulong, MethodSnapshot?>();
        MethodSnapshot? Snapshot(ulong entry)
        {
            if (lifts.TryGetValue(entry, out var known)) return known;
            try
            {
                return lifts[entry] = lifter.Lift(entry).Snapshot;
            }
            catch (FlowException)
            {
                return lifts[entry] = null;
            }
        }

        foreach (var item in document.RootElement.EnumerateArray())
        {
            var description = item.GetProperty("case");
            var method = item.GetProperty("method");
            string category = description.GetProperty("category").GetString()!;
            string name = $"{description.GetProperty("type").GetString()}::{description.GetProperty("method").GetString()}";
            bool shown = show.Length > 0 && (show == "all" || name.EndsWith("::" + show, StringComparison.Ordinal));
            var targets = item.GetProperty("mapping").GetProperty("targets");
            if (!targets.TryGetProperty(target, out var places) || places.GetArrayLength() == 0) continue;
            ulong address = Convert.ToUInt64(places[0].GetProperty("address").GetString()!, 16);
            if (Snapshot(address) is not { } snapshot) continue;
            var module = metadata.Load(Path.GetFileNameWithoutExtension(method.GetProperty("assembly").GetString()!));
            if (module is null) continue;
            MethodBody real;
            try
            {
                real = metadata.Body(module, Convert.ToInt32(method.GetProperty("token").GetString()!, 16));
            }
            catch (ExpansionException)
            {
                continue;
            }
            var graph = new EffectGraph(snapshot, real.Method, facts);
            if (shown) Dump(name, graph);
        }
        return 0;
    }

    private static void Dump(string name, EffectGraph graph)
    {
        Console.WriteLine($"== {name}{(graph.Failure is null ? "" : "  事实层：" + graph.Failure)}{(graph.Cyclic ? "  有环" : "")}");
        foreach (var (value, type, index) in graph.Arguments) Console.WriteLine($"  形参 {index}: {type.Kind}/{type.StorageBits} = {value}");
        foreach (int b in graph.Order)
        {
            var block = new BlockId(b);
            Console.WriteLine($"  B{b}{(graph.Tail(block) is var tail && tail != default ? $"  只抛出尾 {tail}" : "")}");
            for (int i = 0; i < graph.Snapshot.OccurrenceCount(block); i++)
                if (graph.Effect(new(block, i)) is { } e)
                    Console.WriteLine($"    {i}: {e.Kind} {e.Address}{(e.Kind == NativeEffectKind.Write ? " ← " + e.Value : "")}{(e.Width > 0 ? $"（{e.Width} 位）" : "")}"
                        + $"{(e.Callee is null ? "" : $" {e.Callee.Entity}({string.Join(", ", e.Arguments)}) → {e.Result}")}{e.Class}{(e.Exception != default ? " " + e.Exception : "")} {e.Detail}");
            if (graph.Condition(block) is { } condition) Console.WriteLine($"    条件 {condition}");
            if (graph.Returned(block) is { } returned) Console.WriteLine($"    返回 {returned}   槽 {graph.ReturnSlot(block)}");
        }
        foreach (var check in graph.Checks) Console.WriteLine($"  条件抛出 {EffectRef.Of(check.Edge)}: {check.Condition} = {check.Polarity} ⇒ {check.Exception}");
    }
}
