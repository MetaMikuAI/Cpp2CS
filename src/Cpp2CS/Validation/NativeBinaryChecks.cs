using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Iced.Intel;
using Decoder = Iced.Intel.Decoder;

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
            var normalized = NativeNormalizer.Normalize(native);
            NativeReport.Write(normalized, Path.Combine(outputDirectory, name + ".normalized.json"));
            summaries.Add(new { name, original = NativeReport.Summary(native), normalized = NativeReport.Summary(normalized) });
        }
        var sampled = new List<object>();
        var sampledExecutions = 0;
        foreach (var image in new[] { arm, x64 })
        {
            var addresses = new HashSet<ulong>();
            var forms = new SortedDictionary<string, int>(StringComparer.Ordinal);
            var outcomes = new SortedDictionary<string, int>(StringComparer.Ordinal);
            var samples = new List<object>();
            foreach (var entry in SampleEntries(image, 32))
            {
                var region = RegionBuilder.Build(image, [entry], 64);
                var native = StateSsaConverter.Convert(region);
                var normalized = NativeNormalizer.Normalize(native);
                foreach (var block in region.Blocks)
                    if (block.Instruction is { } instruction && addresses.Add(block.Address))
                        forms[instruction.Rule] = forms.GetValueOrDefault(instruction.Rule) + 1;
                var executed = 0;
                for (var variant = 0; variant < 4; variant++)
                {
                    var state = SampleState(region, variant);
                    checks += NativeExecutionChecks.Compare(region, entry.Address, state, 64);
                    var witness = MirRegionExecutor.Execute(region, entry.Address, NativeExecutionChecks.Clone(state), 64);
                    var outcome = witness.Outcome + ":" + (witness.LastInstruction?.Stop?.Kind.ToString() ?? witness.Boundary?.Kind.ToString() ?? "completed");
                    outcomes[outcome] = outcomes.GetValueOrDefault(outcome) + 1;
                    executed += witness.Instructions;
                    sampledExecutions++;
                }
                samples.Add(new
                {
                    entry = $"0x{entry.Address:X}", entry.Evidence, finiteExecutions = 4, executedInstructions = executed,
                    original = NativeReport.Summary(native), normalized = NativeReport.Summary(normalized)
                });
            }
            CoreChecks.Require(samples.Count == 32, "all requested executable-byte quantiles have a candidate boundary");
            checks++;
            sampled.Add(new { architecture = image.Architecture.ToString(), uniqueInstructionAddresses = addresses.Count, forms, outcomes, samples });
        }
        using var assembly = File.OpenRead(typeof(NativeBinaryChecks).Assembly.Location);
        var report = new
        {
            passed = true, mirSchema = MirJson.SchemaVersion, semantics = MirJson.SemanticsVersion,
            implementationAssemblySha256 = Convert.ToHexString(SHA256.HashData(assembly)),
            arm64Sha256 = arm.Sha256, x64Sha256 = x64.Sha256,
            finiteExecutions = 128 + sampledExecutions, documentedWindowExecutions = 128, sampledExecutions, checks,
            sampledRegionsPerArchitecture = 32, regionDecodeBudget = 64, executionInstructionBudget = 64,
            compared = "every executed instruction: slots, memory, flags, reservations, events, schedules, choices, selected edges and stop location",
            limits = "Finite MIR/N1/N2 differential on supplied inputs and sampled open regions; shared operation evaluator is not an independent ISA oracle. Candidate seeds do not establish method entries. No game execution, all-function CFG, ABI summary, concurrency or hardware exception proof",
            regions = summaries, sampled
        };
        var path = Path.Combine(outputDirectory, "native-checks.json");
        File.WriteAllText(path, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
        Console.WriteLine($"native binary checks passed: {checks}; {Path.GetFullPath(path)}");
    }

    private static IEnumerable<EntrySeed> SampleEntries(ImageDocument image, int count)
    {
        var bytes = image.ExecutableRanges.Aggregate(0UL, (total, range) => total + range.FileSize);
        var targets = Enumerable.Range(0, count).Select(i => bytes * (ulong)(2 * i + 1) / (ulong)(2 * count)).ToArray();
        var next = 0;
        ulong preceding = 0;
        foreach (var range in image.ExecutableRanges)
        {
            if (image.Architecture == Architecture.Arm64)
            {
                while (next < count && targets[next] < preceding + range.FileSize)
                {
                    var address = (range.Address + targets[next] - preceding + 3) & ~3UL;
                    if (address + 4 <= range.Address + range.FileSize)
                        yield return new(address, "executable-byte quantile; aligned candidate, not a proven method entry");
                    next++;
                }
            }
            else
            {
                var decoder = Decoder.Create(64, new SampleCodeReader(image.Bytes, checked((int)range.FileOffset), checked((int)range.FileSize)));
                decoder.IP = range.Address;
                while (decoder.IP < range.Address + range.FileSize && next < count && targets[next] < preceding + range.FileSize)
                {
                    decoder.Decode(out var instruction);
                    if (instruction.Length <= 0) throw new InvalidDataException("Sample decoder did not advance");
                    var offset = preceding + instruction.IP - range.Address;
                    if (offset < targets[next]) continue;
                    yield return new(instruction.IP, "executable-byte quantile; Iced linear-sweep boundary, not a proven method entry");
                    next++;
                }
            }
            preceding += range.FileSize;
        }
    }

    private static MachineState SampleState(RegionRevision region, int variant)
    {
        var state = new MachineState();
        if (variant != 3)
        {
            foreach (var (name, width) in StateLayout.For(region.Architecture))
                state.Slots[name] = variant switch
                {
                    0 => BigInteger.Zero,
                    1 => MirOperationEvaluator.Mask(width),
                    _ => new BigInteger(0xA5A5A5A5A5A5A5A5UL) & MirOperationEvaluator.Mask(width)
                };
            state.Slots[region.Architecture == Architecture.Arm64 ? "fpcr" : "mxcsr"] =
                region.Architecture == Architecture.Arm64 ? 0 : 0x1F80;
            state.Slots[region.Architecture == Architecture.Arm64 ? "sp" : "rsp"] = 0x70000100;
        }
        foreach (var block in region.Blocks) state.CodeGuardedPages[block.Address >> 12] = false;
        for (var i = 0; i < 512; i++) state.Memory[0x70000000UL + (ulong)i] = (byte)i;
        for (var i = 0; i < 128; i++)
        {
            state.ChoiceInputs.Enqueue(0);
            state.ExclusiveStoreDecisions.Enqueue(false);
        }
        return state;
    }

    private sealed class SampleCodeReader(ReadOnlyMemory<byte> bytes, int offset, int length) : CodeReader
    {
        private int position = offset;
        private readonly int end = checked(offset + length);
        public override int ReadByte() => position < end ? bytes.Span[position++] : -1;
    }
}
