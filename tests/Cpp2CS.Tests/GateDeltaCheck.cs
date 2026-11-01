using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Cpp2CS.Tests;

/// <summary>门禁比较工具的自检：相同产物判为零差异，人为构造的各类差异都能报出，忽略表与映射只放过声明的部分。</summary>
internal static class GateDeltaCheck
{
    private const string Method = "N.T::M()";

    [Command("gate-delta-tools", "门禁比较工具能报出人为构造的差异，并放过忽略表与映射声明的部分", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var root = Path.Combine(Path.GetTempPath(), "cpp2cs-gate-delta-" + Guid.NewGuid().ToString("N"));
        try
        {
            var before = Write(Path.Combine(root, "before"), new());
            int Delta(Sample sample, Func<string, string, int> tool)
            {
                var after = Write(Path.Combine(root, "after-" + Guid.NewGuid().ToString("N")), sample);
                return Quiet(() => tool(before, after));
            }

            a.Equal(0, Delta(new(), GateDelta.Publications), "publication-delta：相同产物零差异");
            a.Equal(1, Delta(new() { Cil = "CD" }, GateDelta.Publications), "publication-delta：CIL 指纹变化");

            a.Equal(0, Delta(new(), RecoveryArtifactsCheck.Delta), "recovery-delta：相同产物零差异");
            a.Equal(1, Delta(new() { Status = "hole" }, RecoveryArtifactsCheck.Delta), "recovery-delta：已有字段变化");
            a.Equal(1, Delta(new() { ExtraField = true }, RecoveryArtifactsCheck.Delta), "recovery-delta：新增字段自动纳入比较");
            a.Equal(1, Delta(new() { SwapRows = true }, RecoveryArtifactsCheck.Delta), "recovery-delta：行次序变化");
            a.Equal(1, Delta(new() { HoleWithoutCode = true }, RecoveryArtifactsCheck.Delta), "recovery-delta：洞缺少 code 时报差异而不抛异常");

            a.Equal(0, Delta(new(), (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：相同产物零差异");
            a.Equal(1, Delta(new() { TypeVersion = 4 }, (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：TypeVersion 变化");
            a.Equal(0, Delta(new() { TypeVersion = 4 }, (l, r) => GateDelta.Trace(l, r, ["--ignore-type-version"])), "trace-delta：可忽略 TypeVersion");
            a.Equal(1, Delta(new() { Selected = "Y" }, (l, r) => GateDelta.Trace(l, r, ["--ignore-type-version"])), "trace-delta：调用解析的选择变化");
            a.Equal(0, Delta(new() { Milliseconds = 9.75 }, (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：忽略毫秒");
            a.Equal(1, Delta(new() { OutputTypes = 3 }, (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：OutputTypes 序列变化");
            a.Equal(0, Delta(new() { StepName = "renamed" }, (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：步骤序列变化只作诊断");
            var map = Path.Combine(root, "map.tsv");
            File.WriteAllLines(map, ["# 旧名\t新名", "rule\trenamed"]);
            a.Equal(1, Delta(new() { RuleName = "renamed" }, (l, r) => GateDelta.Trace(l, r, [])), "trace-delta：规则记录改名");
            a.Equal(0, Delta(new() { RuleName = "renamed" }, (l, r) => GateDelta.Trace(l, r, ["--map", map])), "trace-delta：按映射改名后相同");

            a.Equal(0, Delta(new(), (l, r) => CilDelta.Run(l, r, Path.Combine(root, "cil-same"), ["--strict"])), "cil-delta --strict：相同产物零差异");
            a.Equal(1, Delta(new() { Constant = 2 }, (l, r) => CilDelta.Run(l, r, Path.Combine(root, "cil-changed"), ["--strict"])), "cil-delta --strict：CIL 变化即失败");
            a.Equal(0, Delta(new() { Constant = 2 }, (l, r) => CilDelta.Run(l, r, Path.Combine(root, "cil-loose"), [])), "cil-delta 默认模式只记录变化");
            a.Equal(1, Delta(new() { AddedMethod = true }, (l, r) => CilDelta.Run(l, r, Path.Combine(root, "cil-added"), ["--strict"])), "cil-delta --strict：新增写出即失败");

            a.Equal(0, Delta(new() { RunId = "other", Milliseconds = 3.5 }, OutputIdentityCheck.Run), "same-output：run.json 与 analysis.jsonl 按忽略表跳过");
            a.Equal(1, Delta(new() { RuleName = "renamed" }, OutputIdentityCheck.Run), "same-output：rules.jsonl 逐字节比较");
            a.Equal(1, Delta(new() { Constant = 2 }, OutputIdentityCheck.Run), "same-output：程序集 CIL 变化");
            a.Equal(0, Delta(new() { Milliseconds = 7.25 }, OutputIdentityCheck.Run), "same-output：source-passes.jsonl 只差耗时");
            a.Equal(1, Delta(new() { SourceChanged = true }, OutputIdentityCheck.Run), "same-output：source-passes.jsonl 去掉耗时后仍不同");

            var facts = Path.Combine(root, "facts");
            foreach (var side in new[] { "l", "r", "x" })
            {
                Directory.CreateDirectory(Path.Combine(facts, side));
                File.WriteAllText(Path.Combine(facts, side, "cold-facts.json"), side == "x" ? """{"Snapshot":{"Accepted":[2]}}""" : """{"Snapshot":{"Accepted":[1]}}""");
                File.WriteAllText(Path.Combine(facts, side, "cold-samples.json"), "[]");
            }
            a.Equal(0, Quiet(() => GateDelta.Facts(Path.Combine(facts, "l"), Path.Combine(facts, "r"))), "facts-delta：相同事实零差异");
            a.Equal(1, Quiet(() => GateDelta.Facts(Path.Combine(facts, "l"), Path.Combine(facts, "x"))), "facts-delta：事实变化");

            var census = Path.Combine(root, "census");
            foreach (var (side, seconds, hits) in new[] { ("l", 600, 5), ("r", 612, 5), ("x", 600, 6) })
            {
                Directory.CreateDirectory(Path.Combine(census, side));
                File.WriteAllLines(Path.Combine(census, side, "idioms.txt"), [$"L2 惯用法普查：10 个函数，{seconds} s；失败 0；无残余 9（90.0%）", $"  guard {hits}"]);
                File.WriteAllLines(Path.Combine(census, side, "idiom-residuals.tsv"), ["kind\tcategory\tcount\tsamples"]);
                File.WriteAllLines(Path.Combine(census, side, "template-instances.jsonl"), []);
            }
            a.Equal(0, Quiet(() => GateDelta.Census(Path.Combine(census, "l"), Path.Combine(census, "r"))), "census-delta：只差耗时时零差异");
            a.Equal(1, Quiet(() => GateDelta.Census(Path.Combine(census, "l"), Path.Combine(census, "x"))), "census-delta：模板命中变化");

            a.True(OutputIdentityCheck.IsIgnored("execution-0-of-4.tsv") && OutputIdentityCheck.IsIgnored("accessor-verified-only.tsv")
                && !OutputIdentityCheck.IsIgnored("rules.jsonl") && !OutputIdentityCheck.IsIgnored("recovery.jsonl"), "忽略表只匹配声明的文件");
        }
        finally
        {
            if (Directory.Exists(root)) Directory.Delete(root, recursive: true);
        }
        return a.Finish("gate-delta-tools");
    }

    private sealed record Sample
    {
        public string Status { get; init; } = "emitted";
        public bool ExtraField { get; init; }
        public bool SwapRows { get; init; }
        public bool HoleWithoutCode { get; init; }
        public string Cil { get; init; } = "AB";
        public int TypeVersion { get; init; } = 3;
        public string Selected { get; init; } = "X";
        public double Milliseconds { get; init; } = 1.5;
        public int OutputTypes { get; init; } = 2;
        public string StepName { get; init; } = "step";
        public string RuleName { get; init; } = "rule";
        public int Constant { get; init; } = 1;
        public bool AddedMethod { get; init; }
        public string RunId { get; init; } = "run";
        public bool SourceChanged { get; init; }
    }

    private static string Write(string directory, Sample s)
    {
        Directory.CreateDirectory(Path.Combine(directory, "assemblies"));
        var hole = s.HoleWithoutCode
            ? """{"address":"0x14","reason":"r","derived":false}"""
            : """{"address":"0x14","reason":"r","derived":false,"code":"recovery.x","category":"x","id":1,"causeId":null}""";
        string[] recovery =
        [
            $$"""{"address":"0x10","method":"{{Method}}","status":"{{s.Status}}","bytes":8,"holes":[]{{(s.ExtraField ? ",\"extra\":1" : "")}}}""",
            $$"""{"address":"0x20","method":"N.T::H()","status":"hole","bytes":8,"holes":[{{hole}}]}""",
        ];
        File.WriteAllLines(Path.Combine(directory, "recovery.jsonl"), s.SwapRows ? recovery.Reverse() : recovery);
        File.WriteAllLines(Path.Combine(directory, "publication.jsonl"),
            [$$"""{"address":"0x10","method":"{{Method}}","assembly":"Sample.dll","token":100663297,"cil":"{{s.Cil}}"}"""]);
        File.WriteAllLines(Path.Combine(directory, "call-resolution.jsonl"),
            [$$"""{"entry":"0x10","method":"{{Method}}","site":"0x14","NativeEntry":32,"TypeVersion":{{s.TypeVersion}},"Status":"bound","selected":"{{s.Selected}}","candidates":[]}"""]);
        File.WriteAllLines(Path.Combine(directory, "analysis.jsonl"),
            [$$"""{"entry":"0x10","method":"{{Method}}","steps":[{"Rule":"{{s.StepName}}","InputVersion":0,"OutputVersion":1,"InputTypes":0,"OutputTypes":{{s.OutputTypes}},"Milliseconds":{{s.Milliseconds}},"Kind":"analysis","Invalidates":null}],"passes":[{"Name":"p","Changed":true,"InputStatements":3,"OutputStatements":2,"Rounds":1,"Convergence":"Converged","Milliseconds":{{s.Milliseconds}}}]}"""]);
        File.WriteAllLines(Path.Combine(directory, "rules.jsonl"),
            [$$"""{"entry":"0x10","method":"{{Method}}","Rule":"{{s.RuleName}}","Site":20,"status":"Applied","Code":null,"Detail":null,"Evidence":null}"""]);
        File.WriteAllText(Path.Combine(directory, "run.json"), $$"""{"runId":"{{s.RunId}}"}""");
        File.WriteAllLines(Path.Combine(directory, "source-passes.jsonl"),
            [$$"""{"method":"{{Method}}","steps":[{"Rule":"source.normalize","Changed":{{(s.SourceChanged ? "true" : "false")}},"InputStatements":1,"OutputStatements":1,"Milliseconds":{{s.Milliseconds}}}]}"""]);
        var tokens = WriteModule(Path.Combine(directory, "assemblies", "Sample.dll"), s.Constant, s.AddedMethod);
        File.WriteAllLines(Path.Combine(directory, "emitted.tsv"), tokens.Select((token, i) =>
            $"Sample.dll\tN\tT\t0x{0x10 + 0x10 * i:x}\t{(i == 0 ? Method : "N.T::K()")}\t0x{token:x8}\ttarget"));
        return directory;
    }

    private static uint[] WriteModule(string path, int constant, bool added)
    {
        var module = ModuleDefinition.CreateModule("Sample", ModuleKind.Dll);
        var type = new TypeDefinition("N", "T", TypeAttributes.Public | TypeAttributes.Class, module.TypeSystem.Object);
        module.Types.Add(type);
        foreach (var name in added ? new[] { "M", "K" } : ["M"])
        {
            var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Int32);
            var il = method.Body.GetILProcessor();
            il.Emit(OpCodes.Ldc_I4, constant);
            il.Emit(OpCodes.Ret);
            type.Methods.Add(method);
        }
        module.Write(path);
        using var written = ModuleDefinition.ReadModule(path);
        return written.GetType("N.T").Methods.Select(m => m.MetadataToken.ToUInt32()).ToArray();
    }

    private static int Quiet(Func<int> tool)
    {
        var console = Console.Out;
        Console.SetOut(TextWriter.Null);
        try { return tool(); }
        finally { Console.SetOut(console); }
    }
}
