using System.Text.Json;
using Cpp2CS.Native;

public static class MethodPipelineChecks
{
    private static readonly ulong[] Entries =
    [0x51f7dc4, 0x51f7774, 0x55d684c, 0x55d4ad8, 0x5bea518,
     0x5993d80, 0x5a8b0b0, 0x59938bc, 0x5990f70, 0x5991434, 0x5a8b5f8,
     0x55d02dc, 0x55d02e4, 0x55d03f4, 0x55d9650];

    private sealed record Snapshot(string Text, string[] Problems, string Route, string Semantics);

    public static void Record(string configuration, string directory, bool verify = false)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(configuration))!;
        Directory.CreateDirectory(directory);
        using var session = new RecoverySession(inputs);
        var originalTypes = session.Symbols.DisplayTypes.ToArray();
        var baseline = new Dictionary<ulong, Snapshot>();
        var retained = new List<LiftResult>();
        var rows = new List<object>();
        foreach (var address in Entries)
        {
            var result = session.Recover(address);
            retained.Add(result);
            var text = session.Render(result);
            var snapshot = Take(session, result);
            baseline.Add(address, snapshot);
            File.WriteAllText(Path.Combine(directory, $"0x{address:x}.cs.txt"), text);
            rows.Add(new { address = $"0x{address:x}", result.Method.Name, problems = result.Problems.ToArray(),
                route = snapshot.Route, async = result.Ssa?.CSharp is not null, bodyProblems = result.Ssa?.Body?.Problems, result.Ssa?.OrdinaryProblems });
            if (verify)
            {
                Require(result.Problems.Count == (address == 0x55d03f4 ? 1 : 0), $"0x{address:x}: 恢复状态改变");
                if (result.Ssa?.CSharp is not null)
                {
                    Require(result.Ssa.Projection is not null, "async 必须生成通用语句树");
                    Require(new SemanticWriter(result.TypeSymbols!).Structured(result.Ssa.Projection!) == text, "async 输出必须来自通用输出器");
                }
                session.Save(result, directory);
            }
            Console.WriteLine($"METHOD 0x{address:x}: {result.Method.Name}; problems={result.Problems.Count}; route={snapshot.Route}");
        }
        File.WriteAllText(Path.Combine(directory, "results.json"), JsonSerializer.Serialize(rows, new JsonSerializerOptions { WriteIndented = true }));
        if (!verify) return;
        Require(baseline[0x55d02dc].Route == "ssa", "简单 getter 接入公共 SSA 业务体");
        Require(baseline[0x55d02dc].Text.Contains("_OnGuiAction_k__BackingField"), "getter 不得恢复成递归属性读取");
        Require(baseline[0x55d02e4].Route == "ssa" && baseline[0x55d02e4].Text.Contains("GCWriteBarrier(ref this._OnGuiAction_k__BackingField)"), "尾调用写屏障通过公共 SSA 证明并保留实际字段");
        Require(baseline[0x55d9650].Route == "ssa-async-single", "单 await 构造模式接入公共语句树");
        Require(session.Symbols.DisplayTypes.SequenceEqual(originalTypes), "方法恢复不写入会话类型表");
        foreach (var address in Entries.Reverse()) Same(baseline[address], Take(session, session.Recover(address)), address);
        foreach (var previous in retained) Same(baseline[previous.Method.Address], Take(session, previous), previous.Method.Address);
        using var fresh = new RecoverySession(inputs);
        foreach (var address in Entries.Reverse()) Same(baseline[address], Take(fresh, fresh.Recover(address)), address);
        Console.WriteLine($"PASS: {Entries.Length} 个方法的重复、逆序、新会话逆序及延迟输出一致");
    }
    private static Snapshot Take(RecoverySession session, LiftResult result) => new(session.Render(result), result.Problems.ToArray(),
        result.Ssa?.Projection?.RecoveryPath ?? result.RecoveryPath,
        JsonSerializer.Serialize(SemanticData.Function(result.Ssa?.Projection ?? result)));
    private static void Same(Snapshot expected, Snapshot actual, ulong address) => Require(expected.Text == actual.Text &&
        expected.Problems.SequenceEqual(actual.Problems) && expected.Route == actual.Route && expected.Semantics == actual.Semantics,
        $"0x{address:x}: 输出、语句树或诊断受恢复顺序影响");
    private static void Require(bool ok, string message) { if (!ok) throw new InvalidOperationException(message); }
}
