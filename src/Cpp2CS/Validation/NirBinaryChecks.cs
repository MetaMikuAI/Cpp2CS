using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Serialization;
using Cpp2CS.Images;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirBinaryChecks
{
    private const ulong ObjectAddress = 0x500000;
    public static void Run(string arm64Path, string x64Path, string outputDirectory)
    {
        Directory.CreateDirectory(outputDirectory);
        var samples = new List<object>();
        var checks = 0;
        var executions = 0;
        foreach (var path in new[] { arm64Path, x64Path })
        {
            var image = ImageDocument.Load(path);
            var arm = image.Architecture == Architecture.Arm64;
            CoreChecks.Require(image.Sha256 == (arm
                ? "6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB"
                : "76C216E8E3F676313040713BC7CB6C9DB4CDB1A230E361C3B9F4BE9E9194CA92"), "NIR binary sample identity");
            checks++;
            var source = new BinarySource(image);
            var unbox = arm ? 0x49F7BDCUL : 0x18029FAB0UL;
            var trampoline = arm ? 0x49C1D94UL : 0x18033CE50UL;
            var rank = arm ? 0x49C1578UL : 0x180389430UL;
            var caller = arm ? 0x49C2080UL : 0x1803899E0UL;
            var callee = arm ? 0x49B9D2CUL : 0x180009350UL;
            RequireBytes(image, unbox, arm ? "00400091C0035FD6" : "488D4110C3");
            RequireBytes(image, trampoline, arm ? "92D70014" : "E95B2CF6FF");
            RequireBytes(image, rank, arm ? "00C84439C0035FD6" : "0FB6812E010000C3");
            RequireBytes(image, caller, arm ? "FE0F1FF82ADFFF97E003002AFE0741F8C0035FD6" : "4883EC28E867F9C7FF8BC04883C428C3");
            RequireBytes(image, callee, arm ? "001840B9C0035FD6" : "8B4118C3");
            checks += 5;
            var contracts = new[]
            {
                Contract(image.Architecture, "unbox_body", unbox, new(64, RecoveryScalarKind.Address), false,
                    arm ? "ELF .dynsym il2cpp_object_unbox index 295 -> direct B target" : "PE il2cpp_object_unbox export ordinal 184 -> direct JMP target"),
                Contract(image.Architecture, "unbox", trampoline, new(64, RecoveryScalarKind.Address), false,
                    arm ? "ELF .dynsym il2cpp_object_unbox index 295" : "PE il2cpp_object_unbox export ordinal 184"),
                Contract(image.Architecture, "rank", rank, new(32), true,
                    arm ? "ELF .dynsym il2cpp_class_get_rank index 2439" : "PE il2cpp_class_get_rank export ordinal 66"),
                Contract(image.Architecture, "class_count", caller, new(64), true,
                    arm ? "ELF .dynsym il2cpp_image_get_class_count index 874" : "PE il2cpp_image_get_class_count export ordinal 148"),
                Contract(image.Architecture, "read_count", callee, new(32), true,
                    "direct machine call target from the class_count exported entry")
            };
            var recovered = NirRecoveryChecks.Recover(source, contracts, new(TailCallEvidence:
                ImmutableDictionary<ulong, string>.Empty.Add(trampoline,
                    "named export consists solely of a direct branch, preserving entry frame and argument/return channels")));
            CoreChecks.Require(recovered.Complete, NirRecoveryChecks.Explain(recovered));
            var stem = arm ? "arm64" : "x64";
            var contractJson = new JsonSerializerOptions { WriteIndented = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase };
            contractJson.Converters.Add(new JsonStringEnumConverter());
            // CLI 合同文件不隐含尾调用证据；转发入口另在本验证的 GraphOptions 中采用。
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".contracts.json"), JsonSerializer.Serialize(
                contracts.Where(contract => contract.Name != "unbox").ToArray(), contractJson) + Environment.NewLine);
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".nir.json"), NirJson.Serialize(recovered.Module) + Environment.NewLine);
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".nir.txt"), NirText.Format(recovered.Module));
            CoreChecks.Require(recovered.Module.Functions.Single(f => f.Id == "class_count").Blocks
                .SelectMany(b => b.Operations).Count(op => op is NirCall) == 1, "real exported caller preserves one logical call");
            CoreChecks.Require(recovered.Module.Functions.Single(f => f.Id == "unbox").Blocks
                .Any(block => block.Terminator is NirTailCall), "real export trampoline becomes a logical tail call under explicit protocol evidence");
            checks += 3;
            var addresses = recovered.Functions.SelectMany(function => function.Graph.Blocks).Select(block => block.Address).ToArray();
            var space = recovered.Module.MemorySpaces.Single().Id;
            var comparisons = new List<object>();
            foreach (var value in new uint[] { 0, 1, 7, 127, 255, 256, 65535, 0x80000000, uint.MaxValue })
            {
                var data = new byte[512];
                BinaryPrimitives.WriteUInt32LittleEndian(data.AsSpan(24), value);
                var rankOffset = arm ? 0x132 : 0x12E;
                data[rankOffset] = (byte)value;
                foreach (var contract in contracts)
                {
                    var machineState = NirRecoveryChecks.InitialState(image.Architecture, [new BigInteger(ObjectAddress)], addresses);
                    for (var i = 0; i < data.Length; i++) machineState.Memory[ObjectAddress + (ulong)i] = data[i];
                    var machine = NirRecoveryChecks.ExecuteMachine(source, contract.EntryAddress, machineState);
                    var context = new NirExecutionContext(recovered.Module);
                    CoreChecks.Require(context.Memory.Map(new(space, ObjectAddress, data.Length, true), [.. data]) is null,
                        "NIR real sample receives explicit object bytes");
                    var nir = NirInterpreter.Execute(recovered.Module, contract.Name,
                        [NirRuntimeValue.Address(space, 64, ObjectAddress)], context);
                    var expected = contract.Name switch
                    {
                        "unbox_body" or "unbox" => ObjectAddress + 16,
                        "rank" => (byte)value,
                        _ => (ulong)value
                    };
                    CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Length == 1 &&
                        nir.Values[0].Bits == machine.Result && machine.Result == expected,
                        $"real {image.Architecture} {contract.Name} MIR/callee+RET/NIR/byte oracle: {nir.Status} {nir.Detail}");
                    CoreChecks.Require(data.SequenceEqual(Enumerable.Range(0, data.Length).Select(i => machineState.Memory[ObjectAddress + (ulong)i])),
                        "real machine function preserves supplied program memory");
                    CoreChecks.Require(context.Memory.Read(space, ObjectAddress, data.Length).Bytes.SequenceEqual(data),
                        "real NIR function preserves supplied program memory");
                    checks += 4;
                    executions++;
                    comparisons.Add(new { function = contract.Name, input = value, expected, machineInstructions = machine.Instructions, nirSteps = nir.Steps });
                }
            }
            samples.Add(new
            {
                architecture = image.Architecture.ToString(), sha256 = image.Sha256,
                contracts = contracts.Select(contract => new { contract.Name, address = $"0x{contract.EntryAddress:X}", contract.Signature, contract.Assumptions }),
                functions = recovered.Functions.Select(function => new { function.Graph.Contract.Name, function.Complete, function.Statistics, function.Evidence }),
                comparisons
            });
        }
        using var assembly = File.OpenRead(typeof(NirBinaryChecks).Assembly.Location);
        var report = new
        {
            passed = true, format = NirModule.FormatVersion, checks, finiteExecutions = executions,
            implementationAssemblySha256 = Convert.ToHexString(SHA256.HashData(assembly)),
            compared = "complete machine execution through real call target and RET against recovered NIR; logical result and supplied program bytes",
            limits = "Five functions per binary under adopted scalar ABI, logical signatures, valid private frames, sequential memory and normal execution. Tail-call classification has explicit thunk evidence. Finite inputs, not game execution, independent ISA proof or whole-binary NIR coverage. The two binaries are different games; each is compared against its own bytes.",
            samples
        };
        var reportPath = Path.Combine(outputDirectory, "nir-binary-checks.json");
        File.WriteAllText(reportPath, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
        Console.WriteLine($"NIR binary checks passed: {checks}; {Path.GetFullPath(reportPath)}");
    }

    private static FunctionContract Contract(Architecture architecture, string name, ulong entry,
        RecoveryScalarType returned, bool readsMemory, string evidence) => new(name, entry,
        new([new(64, RecoveryScalarKind.Address)], returned),
        architecture == Architecture.Arm64 ? MachineAbiKind.Aapcs64 : MachineAbiKind.WindowsX64,
        new(readsMemory, false, false, false, true, false, false),
        [evidence, "adopted scalar runtime interface; native signature checked against the complete instruction body, not inferred from a managed method name"],
        new(true, true, true, true));

    private static void RequireBytes(ImageDocument image, ulong address, string expected)
    {
        var bytes = Convert.FromHexString(expected);
        var resolution = image.Resolve(address);
        CoreChecks.Require(resolution.FileOffset is not null && resolution.AvailableBytes >= (ulong)bytes.Length &&
            image.Bytes.Span.Slice(checked((int)resolution.FileOffset.Value), bytes.Length).SequenceEqual(bytes),
            $"fingerprinted binary fixture at 0x{address:X}");
    }

    private sealed class BinarySource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }
}
