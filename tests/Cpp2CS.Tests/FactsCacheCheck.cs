using System.Text.Json;
using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Model;
using Cpp2CS.Output;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

internal static class FactsCacheCheck
{
    [Command("facts-cache-storage", "事实缓存的内容校验、失效与检查记录保留", Gate = Gate.Unit)]
    public static int Storage()
    {
        var a = new Assertions();
        var directory = Path.Combine(".cpp2cs", "cache-test-" + Guid.NewGuid().ToString("N"));
        var path = Path.Combine(directory, "latest.cache");
        var key = UnregisteredFactsCache.Key("image", "metadata", "code", "runtime");
        a.True(key != UnregisteredFactsCache.Key("changed", "metadata", "code", "runtime"), "二进制变化失效");
        a.True(key != UnregisteredFactsCache.Key("image", "changed", "code", "runtime"), "元数据变化失效");
        a.True(key != UnregisteredFactsCache.Key("image", "metadata", "changed", "runtime"), "实现变化失效");
        a.True(key != UnregisteredFactsCache.Key("image", "metadata", "code", "changed"), "运行时变化失效");
        a.True(UnregisteredFactsCache.Key("image", "metadata", "code", "runtime/frame-slots=True")
            != UnregisteredFactsCache.Key("image", "metadata", "code", "runtime/frame-slots=False"), "提升开关变化失效");
        UnregisteredMethods.Snapshot snapshot = new([], [new(1, "A/无见证", 2, 0, 0, null)],
            [new("unregistered.analysis", "Warning", 2000, 1000, "完整计数不能由样例重建", ["sample"]),
             new("unregistered.registration", "Error", 100, 2, "拒绝", ["sample"])]);
        a.True(UnregisteredFactsCache.Read(path, key, null) is null, "文件不存在时未命中");
        UnregisteredFactsCache.Write(path, key, snapshot, null);
        var restored = UnregisteredFactsCache.Read(path, key, null)!;
        a.Equal(JsonSerializer.Serialize(snapshot), JsonSerializer.Serialize(restored), "完整判定和检查记录无损");
        a.True(UnregisteredFactsCache.Read(path, new string('0', 64), null) is null, "不同 key 不复用");
        var bytes = File.ReadAllBytes(path);
        bytes[^1] ^= 1;
        File.WriteAllBytes(path, bytes);
        a.True(UnregisteredFactsCache.Read(path, key, null) is null, "内容损坏时不复用");
        File.WriteAllBytes(path, bytes[..100]);
        a.True(UnregisteredFactsCache.Read(path, key, null) is null, "截断时不复用");
        UnregisteredFactsCache.Write(path, key, snapshot, null);
        a.True(UnregisteredFactsCache.Read(path, key, null) is not null, "覆盖旧缓存后可读取");
        var messages = new List<string>();
        UnregisteredFactsCache.Write(Path.Combine(path, "blocked.cache"), key, snapshot, messages.Add);
        a.True(messages.Any(m => m.Contains("无法保存")), "路径不可写时只禁用缓存");
        a.Equal(1, Directory.GetFiles(directory).Length, "只保留一份缓存，无临时文件残留");
        var otherKey = UnregisteredFactsCache.Key("image", "metadata", "other-code", "runtime");
        var versioned = UnregisteredFactsCache.PathFor(directory, key);
        var otherVersion = UnregisteredFactsCache.PathFor(directory, otherKey);
        UnregisteredFactsCache.Write(versioned, key, snapshot, null);
        UnregisteredFactsCache.Write(otherVersion, otherKey, snapshot, null);
        a.True(versioned != otherVersion && UnregisteredFactsCache.Read(versioned, key, null) is not null
            && UnregisteredFactsCache.Read(otherVersion, otherKey, null) is not null, "不同实现版本的缓存同时保留并可读取");
        File.Delete(versioned);
        File.Delete(otherVersion);
        File.Delete(path);
        Directory.Delete(directory);
        return a.Finish("facts-cache-storage");
    }

    [Command("facts-cache", "分进程核对真实缓存前后完整事实与样本 CIL", Arguments = "<binary> <metadata> <output> <cold|warm>")]
    public static int Run(string binary, string metadata, string output, string phase)
    {
        if (phase is not ("cold" or "warm")) throw new ArgumentException("phase 必须为 cold 或 warm");
        var messages = new List<string>();
        var facts = FactsBuilder.Build(binary, metadata, message => { messages.Add(message); Console.Error.WriteLine(message); },
            cacheDirectory: Path.Combine(output, "cache"));
        Directory.CreateDirectory(output);
        var a = new Assertions();
        a.Equal(phase == "warm", messages.Any(m => m.StartsWith("未注册事实缓存：命中")), "命中状态符合测试阶段");
        a.True(!facts.Checks.AnyErrors, "真实事实没有 Error");
        foreach (var method in facts.Unregistered.All)
        {
            a.True(ReferenceEquals(facts.Model.Methods[method.Definition.Index], method.Definition), "定义归属本次模型");
            a.True(method.Witnesses.All(w => ReferenceEquals(w.Instance.Method, method.Definition)), "见证绑定本次定义");
        }
        static object? Value(AbiValue? value) => value is null ? null : new { Type = value.Type.ToString(), value.Passing, value.Pieces };
        var manifest = JsonSerializer.SerializeToUtf8Bytes(new
        {
            Snapshot = facts.Unregistered.Capture(facts),
            Abi = facts.Unregistered.All.Select(m => new { m.Address, This = Value(m.Abi.This),
                Parameters = m.Abi.Parameters.Select(Value), Return = Value(m.Abi.Return), m.Abi.MethodInfo }),
            Checks = facts.Checks.All,
        });
        var samples = Samples(facts, a);
        foreach (var (name, bytes) in new[] { ("facts.json", manifest), ("samples.json", samples) })
        {
            var baseline = Path.Combine(output, "cold-" + name);
            if (phase == "warm") a.True(File.ReadAllBytes(baseline).SequenceEqual(bytes), name + " 跨进程逐字节一致");
            File.WriteAllBytes(Path.Combine(output, phase + "-" + name), bytes);
        }
        File.WriteAllText(Path.Combine(output, phase + "-timings.json"), JsonSerializer.Serialize(facts.Timings));
        Console.WriteLine($"接受 {facts.Unregistered.All.Count}；判定 {facts.Unregistered.Decisions.Count}；检查 {facts.Checks.All.Count}；启动 {facts.Timings["total"]:F3}s");
        return a.Finish("facts-cache-" + phase);
    }

    private static byte[] Samples(ProgramFacts facts, Assertions a)
    {
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        var recovery = new MethodRecovery(facts, types);
        var skeleton = new Skeleton(facts.Model);
        var emitter = new BodyEmitter(skeleton, types);
        // 从当前输入选取实际调用未注册目标的函数。
        var addresses = facts.Unregistered.All.SelectMany(m => m.Witnesses)
            .Select(w => w.Caller).Where(c => facts.EntriesAt(c).Any(e => e.Method is not null)).Distinct().Take(12);
        var rows = new List<object>();
        var emitted = 0;
        foreach (var address in addresses)
        {
            var method = facts.EntriesAt(address).First(e => e.Method is not null).Method!;
            var result = recovery.Recover(method, address);
            var problem = result.Body is null ? "L3 有洞" : emitter.Emit([result.Body]).GetValueOrDefault(result.Body)?.Message;
            var body = problem is null ? skeleton.Method(method.Method).Body : null;
            if (body is not null) emitted++;
            string? Operand(object? operand) => operand switch
            {
                Instruction target => "label:" + body!.Instructions.IndexOf(target),
                Instruction[] targets => "labels:" + string.Join(',', targets.Select(t => body!.Instructions.IndexOf(t))),
                _ => operand?.ToString(),
            };
            rows.Add(new { address, method = method.ToString(), result.Holes, problem,
                locals = body?.Variables.Select(v => v.VariableType.FullName).ToArray(),
                il = body?.Instructions.Select(i => new { op = i.OpCode.Name, operand = Operand(i.Operand) }).ToArray(),
                handlers = body?.ExceptionHandlers.Select(h => new { h.HandlerType, type = h.CatchType?.FullName,
                    start = Operand(h.TryStart), end = Operand(h.TryEnd), handler = Operand(h.HandlerStart),
                    handlerEnd = Operand(h.HandlerEnd), filter = Operand(h.FilterStart) }).ToArray() });
        }
        a.True(emitted > 0, "样本实际写出 CIL");
        Console.WriteLine($"小样本 {rows.Count} 个，写出 {emitted} 个；缺口和 CIL 一并参与对比");
        return JsonSerializer.SerializeToUtf8Bytes(rows);
    }
}
