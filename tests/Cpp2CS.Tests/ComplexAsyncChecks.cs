using System.Text.Json;
using Cpp2CS.Native;

public static class ComplexAsyncChecks
{
    public static void Native(Action<bool, string> check, string config)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(config))!;
        using var session = new RecoverySession(inputs);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        check(managed.MutableField("Sekai.Mysekai.MysekaiTutorialProcessor", "_IsDisableActionButtonSwitch_k__BackingField") == "IsDisableActionButtonSwitch", "自动属性写入有非虚编译器 setter 证明");
        check(managed.MutableField("Cysharp.Threading.Tasks.UniTask", "source") is null, "readonly 字段不能生成对象初始化写入");
        Directory.CreateDirectory("artifacts/complex-compiled");
        foreach (var address in JsonSerializer.Deserialize<string[]>(File.ReadAllText("tests/corpus/complex-async.json"))!)
        {
            var result = session.Recover(Convert.ToUInt64(address[2..], 16));
            session.Save(result, "artifacts/recovered");
            check(result.Problems.Count == 0 && result.Ssa?.Body is { CSharp: not null, Problems.Length: 0 }, address + " 完整 async 主体和协议证明");
            var body = result.Ssa!.Body!;
            if (address == "0x5a8b5f8") check(body.Nodes.Count(n => n.Kind == "store") == 1 && body.CSharp!.Contains("IsDisableActionButtonSwitch = true;"), "await 后业务写入恰好保留一次");
            check(!body.CSharp!.Contains("UNKNOWN"), address + " 输出不含未知表达式");
            var owner = body.Source.Owner;
            var dot = owner.LastIndexOf('.');
            File.WriteAllText($"artifacts/complex-compiled/{address}.cs", "namespace " + owner[..dot] + " { public partial class " + owner[(dot + 1)..] + " {\n" + body.CSharp + "\n} }");
        }
        var task = SsaSemantics.Term("call-result", 128, "original");
        var low = SsaSemantics.Slice(task, 0, 64);
        var high = SsaSemantics.Slice(task, 64, 64);
        check(SsaSemantics.Compose([low, high]).Key == task.Key, "SSA 重组同一返回值的连续片段");
        check(SsaSemantics.Compose([high, low]).Key != task.Key, "反序寄存器不视为原值");
        check(SsaSemantics.Compose([low, SsaSemantics.Number(0)]).Key != task.Key, "被覆盖的后半部分不视为原值");
        var other = SsaSemantics.Term("call-result", 128, "other");
        check(SsaSemantics.Compose([low, SsaSemantics.Slice(other, 64, 64)]).Key != task.Key, "不同调用的 source/token 不得拼成原任务");
        check(session.Image.ReadImmutableScalar(0x1f21338, 4) == 0x3e4ccccd, "只读常量保留 0.2f 的精确位值");
        check(session.Image.ReadImmutableScalar(0xbddb000, 4) is null, "可写全局数据不得折叠为常量");
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var instruction = decoder.Decode(session.Image.Read(0x5993e08, 4), 0x5993e08).Single();
        check(instruction.Operands[1].FloatingPoint == 1.0, "从 Capstone 结构化浮点操作数恢复立即数");
    }
}
