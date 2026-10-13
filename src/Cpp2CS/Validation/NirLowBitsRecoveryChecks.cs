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

public static class NirLowBitsRecoveryChecks
{
    public static int Run()
    {
        var checks = RuleBoundaries() + WidthWitnesses();
        foreach (var architecture in new[] { Architecture.Arm64, Architecture.X64 })
        foreach (var subtract in new[] { false, true })
        {
            var arm = architecture == Architecture.Arm64;
            var source = new NirRecoveryChecks.FixtureSource(architecture, "fixture:low-bits");
            source.Add(0x1000, arm ? [subtract ? "000001CB" : "0000018B", "C0035FD6"]
                : subtract ? ["4889C8", "4829D0", "C3"] : ["488D0411", "C3"]);
            var contract = NirRecoveryChecks.Contract(architecture, "low_bits", 0x1000, 2, 32);
            checks += Compare(source, contract, source.Addresses, (a, b) => subtract ? a - b : a + b);

            var shifted = new NirRecoveryChecks.FixtureSource(architecture, "fixture:low-bits-shifted");
            shifted.Add(0x1000, arm ? [subtract ? "000001CB" : "0000018B", "00FC41D3", "C0035FD6"]
                : subtract ? ["4889C8", "4829D0", "48D1E8", "C3"] : ["488D0411", "48D1E8", "C3"]);
            var rejected = NirRecovery.RecoverOne(shifted, contract, new([contract]));
            CoreChecks.Require(!rejected.Complete && rejected.Gaps.Any(gap => gap.Code == "contract.machine-input"),
                "a shifted 32-bit result still depends on unbound input bit 32");
            var missing = contract with { Signature = contract.Signature with { Arguments = [new(32)] } };
            var missingInput = NirRecovery.RecoverOne(source, missing, new([missing]));
            CoreChecks.Require(!missingInput.Complete && missingInput.Gaps.Any(gap => gap.Code == "contract.machine-input"),
                "low-bit arithmetic cannot invent an absent input operand");
            checks += 2;
        }
        return checks;
    }

    public static int RunBinary(string binaryPath, string inventoryDirectory, string? outputPath = null)
    {
        const ulong entry = 0x182C67FB0;
        var image = ImageDocument.Load(binaryPath);
        CoreChecks.Require(image.Architecture == Architecture.X64 &&
            image.Sha256 == "76C216E8E3F676313040713BC7CB6C9DB4CDB1A230E361C3B9F4BE9E9194CA92",
            "low-bit real sample binary fingerprint");
        var manifestPath = Path.Combine(inventoryDirectory, "x64.json");
        if (!File.Exists(manifestPath)) manifestPath = Path.Combine(inventoryDirectory, "x64.inventory.json");
        using var manifest = JsonDocument.Parse(File.ReadAllText(manifestPath));
        var root = manifest.RootElement;
        CoreChecks.Require(root.GetProperty("binary").GetProperty("sha256").GetString() == image.Sha256,
            "low-bit sample inventory binary identity");
        var metadata = root.GetProperty("metadata");
        using var stream = File.OpenRead(metadata.GetProperty("path").GetString()!);
        var metadataHash = Convert.ToHexString(SHA256.HashData(stream));
        CoreChecks.Require(metadataHash == metadata.GetProperty("sha256").GetString() &&
            metadataHash == "FE9899CBF26DCB3071547DEE56518E7C5101C6462FBECB32E505AB2A34031224",
            "low-bit sample metadata identity");
        JsonElement? record = null;
        foreach (var line in File.ReadLines(Path.Combine(inventoryDirectory, root.GetProperty("entriesFile").GetString()!)))
        {
            using var document = JsonDocument.Parse(line);
            if (document.RootElement.GetProperty("entry").GetString() != "0x182c67fb0") continue;
            record = document.RootElement.Clone();
            break;
        }
        CoreChecks.Require(record is not null && record.Value.GetProperty("signatureStatus").GetString() == "known" &&
            record.Value.GetProperty("methodDefinitions").EnumerateArray().Any(item => item.GetInt32() == 90936),
            "real low-bit sample retains its registered metadata method");
        var options = new JsonSerializerOptions { PropertyNameCaseInsensitive = true };
        options.Converters.Add(new JsonStringEnumConverter());
        var contract = record!.Value.GetProperty("contract").Deserialize<FunctionContract>(options)!;
        CoreChecks.Require(contract.EntryAddress == entry && contract.Signature.Arguments.Length == 3 &&
            contract.Signature.Arguments[0] is { Kind: RecoveryScalarKind.Integer, Width: 32 } &&
            contract.Signature.Arguments[1] is { Kind: RecoveryScalarKind.Integer, Width: 32 } &&
            contract.Signature.Arguments[2] is { Kind: RecoveryScalarKind.Address, Width: 64 } &&
            contract.Signature.Result is { Kind: RecoveryScalarKind.Integer, Width: 32 },
            "real low-bit signature comes from two UInt32 parameters and trailing MethodInfo");
        var bytes = Convert.FromHexString("8D810928FFFFC1E00A03C2C3");
        var range = image.Resolve(entry);
        CoreChecks.Require(range.FileOffset is { } offset && range.AvailableBytes >= (ulong)bytes.Length &&
            image.Bytes.Span.Slice((int)offset, bytes.Length).SequenceEqual(bytes), "real LEA/SHL/ADD/RET sample bytes");
        var checks = 6 + Compare(new BinarySource(image), contract, [entry, entry + 6, entry + 9, entry + 11],
            (a, b) => ((a - 0xD7F7) << 10) + b);
        if (outputPath is not null)
        {
            using var inventoryStream = File.OpenRead(manifestPath);
            using var assemblyStream = File.OpenRead(typeof(NirLowBitsRecoveryChecks).Assembly.Location);
            var report = new
            {
                checks, finiteExecutions = 108, entry = $"0x{entry:X}", binarySha256 = image.Sha256, metadataSha256 = metadataHash,
                inventorySha256 = Convert.ToHexString(SHA256.HashData(inventoryStream)),
                inventoryEntriesSha256 = root.GetProperty("entriesSha256").GetString(),
                implementationAssemblySha256 = Convert.ToHexString(SHA256.HashData(assemblyStream)),
                bytes = Convert.ToHexString(bytes), prototype = record.Value.GetProperty("contract"),
                prototypeEvidence = record.Value.GetProperty("signatureEvidence"),
                meaning = "Fingerprint-bound real machine sample and 108 finite MIR/NIR/u32 arithmetic comparisons; no game runtime equivalence claim."
            };
            File.WriteAllText(outputPath, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + Environment.NewLine);
        }
        return checks;
    }

    private static int Compare(IRegionInstructionSource source, FunctionContract contract, IEnumerable<ulong> addresses,
        Func<BigInteger, BigInteger, BigInteger> oracle)
    {
        var recovered = NirRecovery.RecoverOne(source, contract, new([contract]));
        CoreChecks.Require(recovered.Complete, "low-bit recovery: " + NirRecoveryChecks.Explain(recovered));
        var json = NirJson.Serialize(recovered.Module);
        var module = NirJson.Deserialize(json);
        CoreChecks.Require(NirValidator.Validate(module).IsValid && NirJson.Serialize(module) == json,
            "low-bit NIR is valid after a standalone JSON round trip");
        var checks = 2;
        BigInteger[] lows = [0, 1, 0xD7F7, 0x7FFFFFFF, 0x80000000, uint.MaxValue];
        BigInteger[] highs = [0, 0x12345678, uint.MaxValue];
        foreach (var left in lows)
        foreach (var right in lows)
        foreach (var high in highs)
        {
            var state = NirRecoveryChecks.InitialState(source.Architecture, [], addresses);
            state.Slots[source.Architecture == Architecture.Arm64 ? "x0" : "rcx"] = (high << 32) | left;
            state.Slots[source.Architecture == Architecture.Arm64 ? "x1" : "rdx"] = ((high ^ uint.MaxValue) << 32) | right;
            var machine = NirRecoveryChecks.ExecuteMachine(source, contract.EntryAddress, state);
            var arguments = ImmutableArray.CreateBuilder<NirRuntimeValue>();
            arguments.Add(NirRuntimeValue.Integer(32, left));
            arguments.Add(NirRuntimeValue.Integer(32, right));
            if (contract.Signature.Arguments.Length == 3) arguments.Add(NirRuntimeValue.Address("memory", 64, 0));
            var nir = NirInterpreter.Execute(module, contract.Name, arguments.ToImmutable());
            var expected = oracle(left, right) & uint.MaxValue;
            CoreChecks.Require(nir.Status == NirExecutionStatus.Returned && nir.Values.Single().Bits == expected &&
                (machine.Result & uint.MaxValue) == expected, "low-bit MIR/NIR/oracle comparison with arbitrary upper input bits");
            checks++;
        }
        return checks;
    }

    private static int RuleBoundaries()
    {
        var origin = new InstructionOrigin("fixture:low-rule", 0x1000, 0, new byte[4]);
        NativeValue Value(int id, int width) => new(new(id), new BitsType(width));
        var left = Value(0, 64);
        var right = Value(1, 64);
        var wide = new NativeNode(OpCode.Add, Value(2, 64), [left, right], NoPayload.Instance, null, new(origin, 0));
        var low = new NativeNode(OpCode.Extract, Value(3, 32), [wide.Result!.Value], new ImmediatePayload(0), null, new(origin, 1));
        var otherUse = new NativeNode(OpCode.Sub, Value(4, 64), [wide.Result.Value, left], NoPayload.Instance, null, new(origin, 2));
        var definitions = new Dictionary<ValueId, NativeNode> { [wide.Result.Value.Id] = wide };
        CoreChecks.Require(NativePureRules.TryReduce(low, definitions) is null,
            "mechanical normalization does not allocate nodes across MIR stages");
        var allocations = 0;
        NativeValue Narrow(NativeValue value, int width) { allocations++; return Value(10 + allocations, width); }
        CoreChecks.Require(NativePureRules.TryReduce(low with { Payload = new ImmediatePayload(1) }, definitions, Narrow) is null && allocations == 0,
            "nonzero-offset arithmetic slices retain low-bit carry and borrow dependencies");
        var next = 5;
        var reduced = NativePurePass.Run([wide, low, otherUse], null, (source, value, width) =>
            new(OpCode.Extract, Value(next++, width), [value], new ImmediatePayload(0), null, source.Source));
        CoreChecks.Require(reduced.Nodes.Any(node => node.Result == wide.Result && node.Code == wide.Code && node.Inputs.SequenceEqual(wide.Inputs)) &&
            reduced.Nodes.Any(node => node.Result == low.Result && node.Code == OpCode.Add && node.Inputs.All(value => value.Type == new BitsType(32))) &&
            reduced.Rewrites.Any(rewrite => rewrite.Rule == "extract.low-arithmetic"),
            "narrowing creates independent operands and preserves the original shared wide definition");
        return 3;
    }

    private static int WidthWitnesses()
    {
        var checks = 0;
        foreach (var width in new[] { 1, 8, 16, 32, 64, 128 })
        foreach (var code in new[] { OpCode.Add, OpCode.Sub, OpCode.Not })
        {
            var sourceWidth = width + 37;
            var origin = new InstructionOrigin("fixture:low-widths", 0x1000, 0, new byte[4]);
            NativeValue Value(int id, int bits) => new(new(id), new BitsType(bits));
            var left = Value(0, sourceWidth);
            var right = Value(1, sourceWidth);
            var wide = new NativeNode(code, Value(2, sourceWidth), code == OpCode.Not ? [left] : [left, right],
                NoPayload.Instance, null, new(origin, 0));
            var low = new NativeNode(OpCode.Extract, Value(3, width), [wide.Result!.Value], new ImmediatePayload(0), null, new(origin, 1));
            var next = 4;
            var reduced = NativePurePass.Run([wide, low], null, (source, value, bits) =>
                new(OpCode.Extract, Value(next++, bits), [value], new ImmediatePayload(0), null, source.Source));
            var mask = (BigInteger.One << width) - 1;
            BigInteger[] lows = [0, 1, BigInteger.One << (width - 1), mask];
            BigInteger[] highs = [0, 0x12345678, (BigInteger.One << 37) - 1];
            foreach (var a in lows)
            foreach (var b in lows)
            foreach (var high in highs)
            {
                var values = new Dictionary<ValueId, BigInteger>
                {
                    [left.Id] = high << width | a,
                    [right.Id] = (((BigInteger.One << 37) - 1) ^ high) << width | b
                };
                foreach (var node in reduced.Nodes)
                {
                    var result = node.Result!.Value;
                    var operation = new Operation(node.Code, new(result.Id.Id, ((BitsType)result.Type).Width),
                        node.Inputs.Select(value => new Value(value.Id.Id, ((BitsType)value.Type).Width)).ToImmutableArray(), node.Payload);
                    var evaluated = MirOperationEvaluator.Evaluate(Architecture.Arm64, operation,
                        node.Inputs.Select(value => values[value.Id]).ToArray(), new MachineState(), origin, node.Source.OperationIndex);
                    CoreChecks.Require(evaluated.Stop is null && evaluated.Choices == 0, "low-bit pure witness has no effects");
                    values[result.Id] = evaluated.Bits;
                }
                var expected = (code == OpCode.Add ? a + b : code == OpCode.Sub ? a - b : ~a) & mask;
                CoreChecks.Require(values[low.Result!.Value.Id] == expected,
                    $"low-bit modulo arithmetic oracle: {code} at width {width}");
                checks++;
            }
        }
        return checks;
    }

    private sealed class BinarySource(ImageDocument image) : IRegionInstructionSource
    {
        private readonly InstructionDecoder decoder = new(image);
        public string ImageId => image.Sha256;
        public Architecture Architecture => image.Architecture;
        public InstructionDecodeResult Decode(ulong address) => decoder.Decode(address);
    }
}
