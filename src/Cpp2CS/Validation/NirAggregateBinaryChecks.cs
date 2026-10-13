using System.Collections.Immutable;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Serialization;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Validation;

public static class NirAggregateBinaryChecks
{
    private const ulong MethodInfo = 0x600000;
    private static readonly JsonSerializerOptions Json = Options();
    private sealed record Sample(int Method, ulong Entry, string Name, string Bytes, string Operation);

    public static void Run(string arm64Path, string x64Path, string inventoryDirectory, string outputDirectory)
    {
        Directory.CreateDirectory(outputDirectory);
        var checks = 0;
        var executions = 0;
        var reports = new List<object>();
        foreach (var path in new[] { arm64Path, x64Path })
        {
            var image = ImageDocument.Load(path);
            var arm = image.Architecture == Architecture.Arm64;
            var stem = arm ? "arm64" : "x64";
            var expectedHash = arm ? "6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB"
                : "76C216E8E3F676313040713BC7CB6C9DB4CDB1A230E361C3B9F4BE9E9194CA92";
            CoreChecks.Require(image.Sha256 == expectedHash, "real aggregate sample binary fingerprint");
            var manifestPath = Path.Combine(inventoryDirectory, stem + ".json");
            if (!File.Exists(manifestPath)) manifestPath = Path.Combine(inventoryDirectory, stem + ".inventory.json");
            using var manifest = JsonDocument.Parse(File.ReadAllText(manifestPath));
            var metadata = manifest.RootElement.GetProperty("metadata");
            using var metadataStream = File.OpenRead(metadata.GetProperty("path").GetString()!);
            var metadataHash = Convert.ToHexString(SHA256.HashData(metadataStream));
            CoreChecks.Require(metadataHash == metadata.GetProperty("sha256").GetString() &&
                metadataHash == (arm ? "A8BA1ECA04A09E640A0FD71AC813B76F9470BC882E856F8382F9936311116BED"
                    : "FE9899CBF26DCB3071547DEE56518E7C5101C6462FBECB32E505AB2A34031224"), "real aggregate sample metadata fingerprint");
            CoreChecks.Require(manifest.RootElement.GetProperty("binary").GetProperty("sha256").GetString() == image.Sha256,
                "aggregate inventory belongs to the tested binary");
            checks += 3;
            Sample[] samples = arm
                ? [new(163360, 0xAD4D670, "op_Addition#060008ef", "0028221E2128231EC0035FD6", "add"),
                   new(163361, 0xAD4D67C, "op_Subtraction#060008f0", "0038221E2138231EC0035FD6", "sub"),
                   new(163362, 0xAD4D688, "op_Multiply#060008f1", "0008221E2108231EC0035FD6", "mul"),
                   new(163371, 0xAD4D728, "op_Implicit#060008fa", "E203271EC0035FD6", "extend")]
                : [new(77703, 0x182CE8690, "op_Addition#060009a0", "4883EC184889542438F30F10442438F30F104C243C48890C24F30F580424F30F584C24040F14C166480F7EC04883C418C3", "add"),
                   new(77704, 0x182CE8840, "op_Subtraction#060009a1", "4883EC1848894C2438F30F10442438F30F104C243C48891424F30F5C0424F30F5C4C24040F14C166480F7EC04883C418C3", "sub"),
                   new(77705, 0x182CE7E10, "op_Multiply#060009a2", "4883EC184889542438F30F10442438F30F104C243C48890C24F30F590424F30F594C24040F14C166480F7EC04883C418C3", "mul")];
            var records = ReadMethods(Path.Combine(inventoryDirectory, manifest.RootElement.GetProperty("methodsFile").GetString()!), samples.Select(sample => sample.Method)
                .Concat(arm ? [] : new[] { 77714 }).ToHashSet());
            var entries = ReadEntries(Path.Combine(inventoryDirectory, manifest.RootElement.GetProperty("entriesFile").GetString()!), samples.Select(sample => sample.Entry).ToHashSet());
            var contracts = new List<FunctionContract>();
            foreach (var sample in samples)
            {
                var record = records[sample.Method];
                var contract = record.GetProperty("contract").Deserialize<FunctionContract>(Json)!;
                CoreChecks.Require(record.GetProperty("name").GetString() == "UnityEngine.CoreModule.dll::UnityEngine.Vector2::" + sample.Name &&
                    contract.EntryAddress == sample.Entry && record.GetProperty("signatureStatus").GetString() == "known",
                    "sample address is backed by the matching metadata method and registered pointer");
                var evidence = record.GetProperty("signatureEvidence").EnumerateArray().ToArray();
                CoreChecks.Require(evidence.Any(item => Kind(item) == "metadata.method" && item.GetProperty("metadataSha256").GetString() == metadataHash) &&
                    evidence.Any(item => Kind(item) == "il2cpp.module-method-pointer" && item.GetProperty("binarySha256").GetString() == image.Sha256) &&
                    evidence.Any(item => Kind(item) == "il2cpp.type-definition-size" && item.GetProperty("instanceSize").GetInt32() == 24) &&
                    evidence.Any(item => Kind(item) == "il2cpp.value-field" && item.GetProperty("byteOffset").GetInt32() == 4),
                    "aggregate size and field offsets have recorded metadata and registration evidence");
                var entry = entries[sample.Entry];
                var entryContract = entry.GetProperty("contract").Deserialize<FunctionContract>(Json)!;
                CoreChecks.Require(entry.GetProperty("signatureStatus").GetString() == "known" &&
                    contract.Signature.Arguments.Length == entryContract.Signature.Arguments.Length &&
                    contract.Signature.Arguments.Zip(entryContract.Signature.Arguments).All(pair => MachineAbi.TypeEquals(pair.First, pair.Second)) &&
                    MachineAbi.TypeEquals(contract.Signature.Result, entryContract.Signature.Result), "entry aliases agree with the sample contract");
                var argumentCount = sample.Operation == "extend" ? 2 : 3;
                CoreChecks.Require(contract.Signature.Arguments.Length == argumentCount &&
                    contract.Signature.Arguments.Take(argumentCount - 1).All(type => Vector(type, 2)) &&
                    contract.Signature.Arguments[^1] is { Kind: RecoveryScalarKind.Address, Width: 64 } &&
                    Vector(contract.Signature.Result!, sample.Operation == "extend" ? 3 : 2), "logical sample signature is the expected Vector2 value interface plus MethodInfo");
                RequireBytes(image, sample.Entry, sample.Bytes);
                checks += 5;
                contracts.Add(contract);
            }
            var source = new BinarySource(image);
            var recovered = NirRecoveryChecks.Recover(source, contracts);
            CoreChecks.Require(recovered.Complete, NirRecoveryChecks.Explain(recovered));
            var serialized = NirJson.Serialize(recovered.Module);
            var detached = NirJson.Deserialize(serialized);
            CoreChecks.Require(NirValidator.Validate(detached).IsValid && !serialized.Contains(image.Sha256, StringComparison.Ordinal) &&
                !serialized.Contains("Aapcs64", StringComparison.Ordinal) && !serialized.Contains("WindowsX64", StringComparison.Ordinal),
                "detached aggregate NIR validates without image or calling-convention dependencies");
            checks += 2;
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".contracts.json"), JsonSerializer.Serialize(contracts, Json) + Environment.NewLine);
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".nir.json"), serialized + Environment.NewLine);
            File.WriteAllText(Path.Combine(outputDirectory, stem + ".nir.txt"), NirText.Format(detached));
            var addresses = recovered.Functions.SelectMany(function => function.Graph.Blocks).Select(block => block.Address).ToArray();
            var comparisons = new List<object>();
            foreach (var sample in samples)
            {
                var contract = contracts.Single(candidate => candidate.EntryAddress == sample.Entry);
                foreach (var left in Inputs())
                foreach (var right in sample.Operation == "extend" ? new BigInteger[] { 0 } : Inputs())
                {
                    var state = NirRecoveryChecks.InitialState(image.Architecture, [], addresses);
                    // AAPCS64 的 HFA 分别使用 s0/s1 和 s2/s3；Windows 的八字节 struct 使用 RCX/RDX。
                    if (arm)
                    {
                        state.Slots["v0"] = left & uint.MaxValue;
                        state.Slots["v1"] = left >> 32;
                        state.Slots["v2"] = right & uint.MaxValue;
                        state.Slots["v3"] = right >> 32;
                        state.Slots["x0"] = MethodInfo;
                        state.Slots["fpcr"] = 0;
                        state.Slots["fpsr"] = 0;
                    }
                    else
                    {
                        state.Slots["rcx"] = left;
                        state.Slots["rdx"] = right;
                        state.Slots["r8"] = MethodInfo;
                        state.Slots["mxcsr"] = 0x1F80;
                    }
                    var executed = NirRecoveryChecks.ExecuteMachine(source, sample.Entry, state);
                    var machineResult = arm ? (state.Slots["v0"] & uint.MaxValue) | ((state.Slots["v1"] & uint.MaxValue) << 32)
                        : state.Slots["rax"];
                    if (sample.Operation == "extend") machineResult |= (state.Slots["v2"] & uint.MaxValue) << 64;
                    var context = Context(detached);
                    ImmutableArray<NirRuntimeValue> arguments = sample.Operation == "extend"
                        ? [NirRuntimeValue.Integer(64, left), NirRuntimeValue.Address("memory", 64, MethodInfo)]
                        : [NirRuntimeValue.Integer(64, left), NirRuntimeValue.Integer(64, right), NirRuntimeValue.Address("memory", 64, MethodInfo)];
                    var nir = NirInterpreter.Execute(detached, contract.Name, arguments, context);
                    var expected = sample.Operation == "extend" ? left : Oracle(left, right, sample.Operation);
                    CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Length == 1 &&
                        nir.Values[0].Bits == expected && machineResult == expected, $"real {stem} {sample.Name}: MIR/NIR/independent binary32 oracle");
                    var rawStatus = (uint)state.Slots[arm ? "fpsr" : "mxcsr"];
                    var canonical = arm ? (rawStatus & 31) | (rawStatus >> 2 & 32)
                        : (rawStatus & 1) | (rawStatus >> 1 & 30) | (rawStatus << 4 & 32);
                    CoreChecks.Require(context.Environment[NirEnvironmentField.FloatingExceptions] == canonical,
                        "real aggregate float operations preserve the same sticky exception state");
                    CoreChecks.Require(state.Slots[arm ? "sp" : "rsp"] == (arm ? NirRecoveryChecks.Stack - 8 : NirRecoveryChecks.Stack + 8),
                        "real aggregate sample executes its complete stack and RET protocol");
                    checks += 3;
                    executions++;
                    comparisons.Add(new { sample.Method, sample.Name, left = left.ToString("X"), right = right.ToString("X"),
                        result = expected.ToString("X"), machineInstructions = executed.Instructions, nirSteps = nir.Steps });
                }
            }
            object? rejected = null;
            if (!arm)
            {
                var record = records[77714];
                var indirect = record.GetProperty("contract").Deserialize<FunctionContract>(Json)!;
                CoreChecks.Require(indirect.EntryAddress == 0x1803E5CD0 && Vector(indirect.Signature.Arguments[0], 2) &&
                    Vector(indirect.Signature.Result!, 3), "real Windows rejection has a Vector3 result requiring hidden storage");
                RequireBytes(image, indirect.EntryAddress, "48895424080F57D2F30F104C240CF30F104424080F14C1F20F1101F30F115108488BC1C3");
                var result = NirRecoveryChecks.Recover(source, [indirect]);
                CoreChecks.Require(!result.Complete && result.Functions.Single().Diagnostics.Any(diagnostic => diagnostic.Code == "graph.UnsupportedInterface"),
                    "real Windows hidden aggregate return remains an explicit unsupported interface");
                checks += 3;
                rejected = new { metadata = record, diagnostics = result.Functions.Single().Diagnostics,
                    reason = "Windows 12-byte aggregate return requires sret storage; no pointer-shaped logical result is invented" };
            }
            reports.Add(new { architecture = stem, binarySha256 = image.Sha256, metadataSha256 = metadataHash,
                samples = samples.Select(sample => new { sample.Method, address = $"0x{sample.Entry:X}", sample.Bytes,
                    metadata = records[sample.Method], statistics = recovered.Functions.Single(function => function.Graph.Contract.EntryAddress == sample.Entry).Statistics }),
                comparisons, rejected });
        }
        using var assembly = File.OpenRead(typeof(NirAggregateBinaryChecks).Assembly.Location);
        var report = new { passed = true, checks, finiteExecutions = executions,
            implementationAssemblySha256 = Convert.ToHexString(SHA256.HashData(assembly)),
            compared = "fingerprinted binary instructions through RET versus serialized standalone NIR and independent finite binary32 arithmetic",
            limits = "Two different games, seven metadata-backed functions; finite exact binary32 inputs, ordinary IL2CPP generated prototypes, normal sequential execution, valid private stack and default floating environment. Not game runtime or whole-binary semantic equivalence.",
            reports };
        var destination = Path.Combine(outputDirectory, "nir-aggregate-binary-checks.json");
        File.WriteAllText(destination, JsonSerializer.Serialize(report, Json) + Environment.NewLine);
        Console.WriteLine($"NIR aggregate binary checks passed: {checks}; {executions} executions; {Path.GetFullPath(destination)}");
    }

    private static bool Vector(RecoveryScalarType type, int fields) => type is { Kind: RecoveryScalarKind.Aggregate, Aggregate: { } layout } &&
        type.Width == fields * 32 && layout.AlignmentBytes == 4 && layout.Fields.Length == fields &&
        layout.Fields.Select((field, index) => field.ByteOffset == index * 4 && field.Type is { Kind: RecoveryScalarKind.Float, Width: 32 }).All(value => value);

    private static BigInteger[] Inputs() =>
        [Pack(0, -0.0f), Pack(1, -2), Pack(0.5f, 16), Pack(-0.125f, 1024), Pack(-3, 7), Pack(8, 0.25f), Pack(32, -64), Pack(-16, -0.5f)];
    private static BigInteger Pack(float x, float y) => new BigInteger(BitConverter.SingleToUInt32Bits(x)) | new BigInteger(BitConverter.SingleToUInt32Bits(y)) << 32;
    private static BigInteger Oracle(BigInteger left, BigInteger right, string operation)
    {
        return Pack(Lane((uint)(left & uint.MaxValue), (uint)(right & uint.MaxValue)), Lane((uint)(left >> 32), (uint)(right >> 32)));

        float Lane(uint a, uint b)
        {
            var x = BitConverter.UInt32BitsToSingle(a);
            var y = BitConverter.UInt32BitsToSingle(b);
            return operation switch { "add" => x + y, "sub" => x - y, "mul" => x * y,
                _ => throw new ArgumentOutOfRangeException(nameof(operation)) };
        }
    }

    private static NirExecutionContext Context(NirModule module)
    {
        var context = new NirExecutionContext(module);
        foreach (var field in new[] { NirEnvironmentField.RoundingMode, NirEnvironmentField.FlushSubnormalInput,
            NirEnvironmentField.FlushSubnormalOutput, NirEnvironmentField.CanonicalNaN, NirEnvironmentField.FloatingTrapMask,
            NirEnvironmentField.FloatingExceptions }) context.Environment.Add(field, 0);
        return context;
    }

    private static Dictionary<int, JsonElement> ReadMethods(string path, HashSet<int> selected)
    {
        var records = new Dictionary<int, JsonElement>();
        foreach (var line in File.ReadLines(path))
        {
            if (!line.Contains("UnityEngine.CoreModule.dll::UnityEngine.Vector2::", StringComparison.Ordinal)) continue;
            using var document = JsonDocument.Parse(line);
            var method = document.RootElement.GetProperty("methodDefinition").GetInt32();
            if (selected.Contains(method)) records.Add(method, document.RootElement.Clone());
        }
        CoreChecks.Require(records.Count == selected.Count, "all selected metadata records are present");
        return records;
    }

    private static Dictionary<ulong, JsonElement> ReadEntries(string path, HashSet<ulong> selected)
    {
        var needles = selected.ToDictionary(entry => $"\"entry\":\"0x{entry:x}\"", entry => entry);
        var records = new Dictionary<ulong, JsonElement>();
        foreach (var line in File.ReadLines(path))
        {
            var match = needles.FirstOrDefault(pair => line.Contains(pair.Key, StringComparison.Ordinal));
            if (match.Key is null) continue;
            using var document = JsonDocument.Parse(line);
            records.Add(match.Value, document.RootElement.Clone());
        }
        CoreChecks.Require(records.Count == selected.Count, "all selected entry records are present");
        return records;
    }

    private static string? Kind(JsonElement evidence) => evidence.TryGetProperty("kind", out var kind) ? kind.GetString() : null;
    private static void RequireBytes(ImageDocument image, ulong address, string expected)
    {
        var bytes = Convert.FromHexString(expected);
        var range = image.Resolve(address);
        CoreChecks.Require(range.FileOffset is { } offset && range.AvailableBytes >= (ulong)bytes.Length &&
            image.Bytes.Span.Slice((int)offset, bytes.Length).SequenceEqual(bytes), "real aggregate instruction bytes match the reviewed sample");
    }
    private static JsonSerializerOptions Options()
    {
        var options = new JsonSerializerOptions { PropertyNameCaseInsensitive = true, PropertyNamingPolicy = JsonNamingPolicy.CamelCase, WriteIndented = true };
        options.Converters.Add(new JsonStringEnumConverter());
        return options;
    }
    private sealed class BinarySource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }
}
