using System.Text.Json;
using Cpp2CS.Native;

public static class FinallyChecks
{
    public static void Run(Action<bool, string> check)
    {
        var reference = new MetadataReference(1, "ScriptMetadata", "Example_TypeInfo", "Example_c*", 0);
        var ensure = new CallStatement(0, "Runtime.EnsureClassInitialized", [new MetadataExpression(reference, false)], null, "void", false, null);
        var instruction = new Instruction(0, "ret", "", [], false, false, "");
        LiftResult View(bool entryInitialized) => ViewNormalizer.Normalize(new(new(0, "Example$$Run", "void", [], ""), [instruction], new()
        {
            [0] = new(0, entryInitialized ? [ensure] : [], null, [1]),
            [1] = new(1, [], new NameExpression("condition"), [2, 3]),
            [2] = new(2, [ensure with { Pc = 2 }], null, [1]),
            [3] = new(3, [ensure with { Pc = 3 }, new ReturnStatement(3, null)], null, [])
        }, [], [], new NativeGraph([instruction], _ => false)));
        int Count(LiftResult result) => result.Blocks.Values.SelectMany(b => b.Statements).OfType<CallStatement>().Count(c => c.Name == ensure.Name);
        check(Count(View(true)) == 1, "循环前初始化可支配循环内和循环后重复初始化");
        check(Count(View(false)) == 2, "循环体初始化不能覆盖零轮路径，也不能删除首次初始化");
    }
    public static void Native(Action<bool, string> check, string path)
    {
        var inputs = JsonSerializer.Deserialize<NativeInputs>(File.ReadAllText(path))!;
        using var session = new RecoverySession(inputs);
        var result = session.Recover(0x58bbcb8);
        session.Save(result, "artifacts/recovered");
        check(result.Problems.Count == 0 && result.Finally is not null, "真实循环清理区域完成证明");
        var text = File.ReadAllText("artifacts/recovered/0x58bbcb8.cs.txt");
        check(new[] { "Runtime.", "MetadataValue", "DisplayClass", "static_fields", "__9", "UNKNOWN", "PARTIAL" }.All(s => !text.Contains(s)), "完整源码没有编译器环境或未知占位");
        var source = session.SourceView(session.View(result)).View;
        var sortKey = false;
        SourceTree.Map(source, expression =>
        {
            if (expression is LambdaExpression { Parameters: [var parameter], Body: var body })
            {
                if (body is OperationExpression { Operation: ValueOperation.IntegerCast, Type: "int32_t", Arguments: [var argument] }) body = argument;
                sortKey |= body is MemberExpression { Receiver: NameExpression receiver, Field.Name: "seq", Field.Type: "int32_t" } && receiver.Name == parameter;
            }
            return expression;
        });
        check(text.Contains("finally") && text.Contains(".Dispose();") && text.Contains(".Current") && sortKey, "完整输出保留枚举协议、清理与排序字段 lambda");
        Directory.CreateDirectory("artifacts/finally");
        var start = text.IndexOf("System.Collections.Generic.List<", StringComparison.Ordinal);
        File.WriteAllText("artifacts/finally/Recovered.cs", "namespace Sekai.Mysekai; public static partial class BulkHarvestMasterUtility { public static " + text[start..] + "\n}");

        var symbols = session.Symbols;
        var layouts = new HeaderLayout(inputs.Header, inputs.Clang);
        using var managed = new ManagedNames(inputs.ManagedAssembly);
        using var decoder = new Arm64Decoder(inputs.Capstone);
        var abi = new NativeAbi(layouts, managed);
        var runtime = new RuntimeProfile(session.Image);
        var equivalents = new NativeBodyEquivalence(session.Image, decoder);
        var program = result.Ssa!.Program;
        var rawGraph = new NativeGraph(result.Instructions, runtime.NoReturn, address => symbols.Unique(address) is not null || runtime.Helpers.ContainsKey(address));
        FinallyLoop? Prove(NativeSsaProgram candidate) => FinallyLoops.Recover(rawGraph,
            new(candidate, result.Method, symbols, layouts, abi, session.Image, runtime, equivalents), abi, runtime);
        check(Prove(program) is not null, "独立 SSA 清理证明可重放");
        NativeSsaProgram Change(Func<SsaValue, SsaValue> f, params SsaValue[] extra) => program with { Values = program.Values.Select(f).Concat(extra).ToArray() };
        var poison = new SsaValue("test_wrong", "constant", 64, [], Immediate: 17);
        check(Prove(Change(v => v.Id == "call_58bc05c" ? v with { Inputs = v.Inputs.Select((x, n) => n == 2 ? poison.Id : x).ToArray() } : v, poison)) is null, "异常路径清理错误接收者时拒绝");
        check(Prove(Change(v => v.Id == "call_58bc068" ? v with { Inputs = v.Inputs.Select((x, n) => n == 2 ? poison.Id : x).ToArray() } : v, poison)) is null, "替换重抛的异常载荷时拒绝");
        check(Prove(Change(v => v.Id == "call_58bc08c" ? v with { Inputs = v.Inputs.Select((x, n) => n == 2 ? poison.Id : x).ToArray() } : v, poison)) is null, "替换展开的原始异常时拒绝");
        check(Prove(Change(v => v.Id == "condition_58bc060" ? v with { Operation = "nonzero" } : v)) is null, "抑制非空异常的分支不满足 finally 条件");
        NativeSsaProgram Edges(ulong address, Func<NativeFlowNode, NativeFlowNode> f) => program with
        { Flow = program.Flow with { Nodes = program.Flow.Nodes.Select(n => n.Instruction.Address == address ? f(n) : n).ToArray() } };
        check(Prove(Edges(0x58bc038, n => n with { Edges = [new(n.Instruction.Address, 0x58bc064, "branch")] })) is null, "异常出口绕过 Dispose 时拒绝");
        check(Prove(Edges(0x58bc060, n => n with { Edges = n.Edges.Select(e => e.Kind == "not-taken" ? e with { Target = 0x58bc054 } : e).ToArray() })) is null, "重复 Dispose 或处理器循环时拒绝");
        check(Prove(program with { Flow = program.Flow with { Nodes = program.Flow.Nodes.Select(n => n with
        { Edges = n.Edges.Select(e => e.Region is { } r ? e with { Region = r with { Actions = r.Actions.Where(a => a.Kind != "cleanup").ToArray() } } : e).ToArray() }).ToArray() } }) is null,
            "缺失 LSDA cleanup 动作时拒绝");
        check(Prove(program with { Problems = ["unsupported operation"] }) is null, "未支持指令不能被清理协议遮蔽");
    }
}
