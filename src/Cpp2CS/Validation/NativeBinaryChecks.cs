using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;

namespace Cpp2CS.Validation;

public static class NativeBinaryChecks
{
    public static void Run(string arm64Path, string x64Path, string outputDirectory)
    {
        Directory.CreateDirectory(outputDirectory);
        var arm = ImageDocument.Load(arm64Path);
        var x64 = ImageDocument.Load(x64Path);
        CoreChecks.Require(arm.Architecture == Architecture.Arm64 &&
            arm.Sha256 == "6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB", "ARM sample identity");
        CoreChecks.Require(x64.Architecture == Architecture.X64 &&
            x64.Sha256 == "76C216E8E3F676313040713BC7CB6C9DB4CDB1A230E361C3B9F4BE9E9194CA92", "x64 sample identity");
        var armEntries = new[] { new EntrySeed(0x55D979C, "binary window documented in NativeIR设计.md; no method-boundary claim") };
        var x64Entries = new[] { new EntrySeed(0x1824362A8, "binary window documented in NativeIR设计.md; no method-boundary claim") };
        var armWindow = RegionBuilder.Build(arm, armEntries, 3);
        var x64Window = RegionBuilder.Build(x64, x64Entries, 5);
        CoreChecks.Require(armWindow.Blocks.Count(b => b.Instruction is not null) == 3, "three ARM instructions in documented window");
        CoreChecks.Require(x64Window.Blocks.Count(b => b.Instruction is not null) == 5, "five x64 instructions in documented window");
        var checks = 4;
        for (var i = 0; i < 64; i++)
        {
            var state = NativeExecutionChecks.State(Architecture.Arm64);
            state.CodeGuardedPages[0x55D979CUL >> 12] = false;
            state.Slots["x9"] = i;
            state.Slots["x10"] = ulong.MaxValue - (ulong)i;
            checks += NativeExecutionChecks.Compare(armWindow, 0x55D979C, state, 3);
        }
        var table = x64.Resolve(0x182436694);
        CoreChecks.Require(table.FileOffset is not null && table.AvailableBytes >= 16, "x64 documented jump table mapping");
        for (var i = 0; i < 64; i++)
        {
            var state = NativeExecutionChecks.State(Architecture.X64);
            state.Slots["rax"] = (1UL << 48) | (uint)(i % 8);
            for (var j = 0; j < 16; j++) state.Memory[0x182436694UL + (ulong)j] = x64.Bytes.Span[(int)table.FileOffset!.Value + j];
            checks += NativeExecutionChecks.Compare(x64Window, 0x1824362A8, state, 5);
        }
        // 扩大图发现范围，但不把有限窗口的执行对照外推到整个区域。
        var regions = new[]
        {
            (Name: "arm64-window", Region: armWindow), (Name: "x64-window", Region: x64Window),
            (Name: "arm64-region", Region: RegionBuilder.Build(arm, armEntries, 128)),
            (Name: "x64-region", Region: RegionBuilder.Build(x64, x64Entries, 128))
        };
        var summaries = new List<object>();
        foreach (var (name, region) in regions)
        {
            var native = StateSsaConverter.Convert(region);
            NativeReport.Write(native, Path.Combine(outputDirectory, name + ".native.json"));
            summaries.Add(new { name, summary = NativeReport.Summary(native) });
        }
        using var assembly = File.OpenRead(typeof(NativeBinaryChecks).Assembly.Location);
        var report = new
        {
            passed = true, mirSchema = MirJson.SchemaVersion, semantics = MirJson.SemanticsVersion,
            implementationAssemblySha256 = Convert.ToHexString(SHA256.HashData(assembly)),
            arm64Sha256 = arm.Sha256, x64Sha256 = x64.Sha256,
            finiteExecutions = 128, armExecutions = 64, x64Executions = 64, checks,
            compared = "every executed instruction: slots, memory, flags, reservations, events, schedules, choices, selected edges and stop location",
            limits = "MIR-to-SSA differential on supplied inputs; shared operation evaluator is not an independent ISA oracle; no game execution, all-function CFG, ABI summary, concurrency or hardware exception proof",
            regions = summaries
        };
        var path = Path.Combine(outputDirectory, "native-checks.json");
        File.WriteAllText(path, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
        Console.WriteLine($"native binary checks passed: {checks}; {Path.GetFullPath(path)}");
    }
}
