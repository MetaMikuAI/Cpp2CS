using Cpp2CS;
using Cpp2CS.Arm64;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Native;
using Cpp2CS.Nir;
using Cpp2CS.Recovery;
using Cpp2CS.Validation;
using Cpp2CS.X64;
using Iced.Intel;
using System.Globalization;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Serialization;

if (args.Length == 1 && args[0] == "selftest") return CoreChecks.Run();
if (args.Length == 1 && args[0] == "validate-nir")
{
    var validation = NirValidator.Validate(NirJson.Deserialize(Console.In.ReadToEnd()));
    Console.WriteLine(JsonSerializer.Serialize(validation, new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase }));
    return validation.IsValid ? 0 : 1;
}
if (args.Length is >= 4 and <= 7 && args[0] == "nir-corpus")
{
    var options = new NirCorpusOptions(
        MaxInstructions: args.Length > 4 ? int.Parse(args[4], CultureInfo.InvariantCulture) : 512,
        MaxMachineDiagnosticInstructions: args.Length > 5 ? int.Parse(args[5], CultureInfo.InvariantCulture) : 32,
        MaxNormalizationRounds: args.Length > 6 ? int.Parse(args[6], CultureInfo.InvariantCulture) : 64);
    return NirCorpusChecks.Run(args[1], args[2], args[3], options) ? 0 : 2;
}
if (args.Length == 4 && args[0] == "nir-check")
{
    NirBinaryChecks.Run(args[1], args[2], args[3]);
    return 0;
}
if (args.Length == 5 && args[0] == "nir-aggregate-check")
{
    NirAggregateBinaryChecks.Run(args[1], args[2], args[3], args[4]);
    return 0;
}
if (args.Length == 4 && args[0] == "nir-low-bits-check")
{
    Console.WriteLine($"NIR real low-bit checks passed: {NirLowBitsRecoveryChecks.RunBinary(args[1], args[2], args[3])}");
    return 0;
}
if (args.Length == 4 && args[0] == "nir")
{
    var image = ImageDocument.Load(args[1]);
    var jsonOptions = new JsonSerializerOptions
    {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase, PropertyNameCaseInsensitive = true,
        WriteIndented = true, UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        RespectNullableAnnotations = true, RespectRequiredConstructorParameters = true
    };
    jsonOptions.Converters.Add(new JsonStringEnumConverter());
    using var document = JsonDocument.Parse(File.ReadAllText(args[2]), new JsonDocumentOptions { AllowDuplicateProperties = false });
    var contracts = document.RootElement.Deserialize<FunctionContract[]>(jsonOptions)
        ?? throw new InvalidDataException("NIR conversion requires an explicit function contract array");
    if (contracts.Length == 0) throw new InvalidDataException("NIR conversion requires at least one function contract");
    var result = NirRecovery.Recover(image, contracts);
    Directory.CreateDirectory(args[3]);
    var modulePath = Path.Combine(args[3], "module.nir.json");
    var reportPath = Path.Combine(args[3], "recovery.json");
    File.WriteAllText(modulePath, NirJson.Serialize(result.Module) + Environment.NewLine);
    File.WriteAllText(Path.Combine(args[3], "module.nir.txt"), NirText.Format(result.Module));
    var report = new
    {
        format = "cpp2cs.nir-recovery/1", result.Complete, sourceSha256 = image.Sha256,
        architecture = image.Architecture.ToString(), module = Path.GetFullPath(modulePath), contracts,
        functions = result.Functions.Select(function => new
        {
            function.Graph.Contract.Name, address = $"0x{function.Graph.Contract.EntryAddress:X}", function.Complete,
            function.Statistics, diagnostics = function.Diagnostics, evidence = function.Evidence,
            graphRevision = function.Graph.Revision, graphDependencies = function.Graph.Dependencies,
            blockMap = function.Function?.Blocks.Select(block => new
            {
                nirBlock = block.Id.Id,
                machineAddress = function.Graph.Blocks.FirstOrDefault(candidate => candidate.Id == block.Id.Id) is { } mapped
                    ? $"0x{mapped.Address:X}" : null
            }),
            sourceInstructions = function.Graph.Blocks.Where(block => block.Instruction is not null).Select(block => new
            {
                block.Id, address = $"0x{block.Address:X}", fileOffset = $"0x{block.Instruction!.Origin.FileOffset:X}",
                bytes = Convert.ToHexString(block.Instruction.Origin.Bytes.Span), block.Instruction.Rule
            })
        }),
        limits = "Conditional native recovery under explicit contracts and domains; incomplete functions remain diagnostics. Managed compiler variables, async, closures and C# reconstruction are outside NIR."
    };
    File.WriteAllText(reportPath, JsonSerializer.Serialize(report, jsonOptions) + Environment.NewLine);
    Console.WriteLine(JsonSerializer.Serialize(new
    {
        result.Complete, functions = result.Module.Functions.Length, drafts = result.Functions.Count(function => !function.Complete),
        module = Path.GetFullPath(modulePath), report = Path.GetFullPath(reportPath)
    }));
    return result.Complete ? 0 : 2;
}
if (args.Length == 4 && args[0] == "native-check")
{
    NativeBinaryChecks.Run(args[1], args[2], args[3]);
    return 0;
}
if (args.Length == 5 && args[0] == "native")
{
    var image = ImageDocument.Load(args[1]);
    var entries = args[2].Split(',').Select(a => new EntrySeed(ParseAddress(a), "explicit CLI entry; not a proved function boundary"));
    var region = RegionBuilder.Build(image, entries, int.Parse(args[3], CultureInfo.InvariantCulture));
    var native = NativeNormalizer.Normalize(StateSsaConverter.Convert(region));
    NativeReport.Write(native, args[4]);
    Console.WriteLine(JsonSerializer.Serialize(new { report = Path.GetFullPath(args[4]), summary = NativeReport.Summary(native) }));
    return 0;
}
if (args.Length == 1 && args[0] == "validate-ir")
{
    Console.WriteLine(MirJson.Serialize(MirJson.Deserialize(Console.In.ReadToEnd())));
    return 0;
}
if (args.Length == 1 && args[0] == "serve")
{
    while (Console.ReadLine() is { } line)
    {
        using var input = JsonDocument.Parse(line, new JsonDocumentOptions { AllowDuplicateProperties = false });
        var root = input.RootElement;
        var architecture = root.GetProperty("arch").GetString() switch
        {
            "arm64" => Architecture.Arm64,
            "x64" => Architecture.X64,
            _ => throw new InvalidDataException("Unsupported architecture")
        };
        var bytes = Convert.FromHexString(root.GetProperty("bytes").GetString()!);
        var address = ParseAddress(root.GetProperty("address").GetString()!);
        bool? decoded = null;
        if (architecture == Architecture.X64)
        {
            var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes));
            decoder.IP = address;
            var instruction = decoder.Decode();
            decoded = !instruction.IsInvalid;
            if (root.TryGetProperty("decodeFirst", out var first) && first.GetBoolean()) bytes = bytes[..instruction.Length];
        }
        var lift = Lift(architecture, new("fixture:differential", address, 0, bytes));
        if (lift.Ir is null)
        {
            Console.WriteLine(JsonSerializer.Serialize(new { supported = false, length = bytes.Length, decoded, lift.Form, lift.Reason }));
            continue;
        }
        var errors = MirValidator.Validate(lift.Ir);
        if (errors.Count != 0) throw new InvalidOperationException(string.Join("; ", errors));
        if (root.TryGetProperty("evaluate", out var evaluate) && !evaluate.GetBoolean())
        {
            Console.WriteLine(JsonSerializer.Serialize(new
            {
                supported = true, length = bytes.Length, decoded, lift.Form, support = lift.Ir.Support.ToString(), operations = lift.Ir.Operations.Length,
                profile = lift.Ir.ProfileId, capabilities = DescribeContract(lift.Ir)
            }));
            continue;
        }
        var state = new MachineState();
        if (root.TryGetProperty("choiceInputs", out var choiceInputs))
            foreach (var choice in choiceInputs.EnumerateArray()) state.ChoiceInputs.Enqueue(ParseBits(choice.GetString()!));
        if (root.TryGetProperty("slots", out var slots))
            foreach (var slot in slots.EnumerateObject())
            {
                var bits = ParseBits(slot.Value.GetString()!);
                if (!StateLayout.For(architecture).TryGetValue(slot.Name, out var width) || bits < 0 || bits > MirInterpreter.Mask(width))
                    throw new InvalidDataException($"Invalid state slot or value: {slot.Name}");
                state.Slots.Add(slot.Name, bits);
            }
        if (root.TryGetProperty("memory", out var memory))
            foreach (var region in memory.EnumerateArray())
            {
                var start = ParseAddress(region.GetProperty("address").GetString()!);
                var data = Convert.FromHexString(region.GetProperty("bytes").GetString()!);
                for (var i = 0; i < data.Length; i++) state.Memory.Add(start + (ulong)i, data[i]);
            }
        if (root.TryGetProperty("reservation", out var reservation) && reservation.ValueKind != JsonValueKind.Null)
        {
            var size = reservation.GetProperty("sizeBytes").GetInt32();
            if (size is not (1 or 2 or 4 or 8 or 16)) throw new InvalidDataException("Invalid reservation size");
            state.Reservation = new(ParseAddress(reservation.GetProperty("address").GetString()!), size);
        }
        if (root.TryGetProperty("exclusiveDecisions", out var decisions))
            foreach (var decision in decisions.EnumerateArray()) state.ExclusiveStoreDecisions.Enqueue(decision.GetBoolean());
        if (root.TryGetProperty("codePages", out var codePages))
            foreach (var page in codePages.EnumerateArray())
            {
                var start = ParseAddress(page.GetProperty("address").GetString()!);
                if ((start & 4095) != 0) throw new InvalidDataException("Code page must be aligned to 4096 bytes");
                state.CodeGuardedPages.Add(start >> 12, page.GetProperty("guarded").GetBoolean());
            }
        if (root.TryGetProperty("schedule", out var schedule))
        {
            var previous = 0;
            foreach (var item in schedule.EnumerateArray())
            {
                var before = item.GetProperty("beforeEvent").GetInt32();
                if (before < previous) throw new InvalidDataException("Schedule event indices must be nonnegative and ordered");
                previous = before;
                var location = item.TryGetProperty("address", out var locationJson) ? ParseAddress(locationJson.GetString()!) : (ulong?)null;
                var data = item.TryGetProperty("bytes", out var dataJson) ? Convert.FromHexString(dataJson.GetString()!) : [];
                var invalidate = item.GetProperty("invalidateExclusive").GetBoolean();
                if (location is null && data.Length != 0 || location is null && !invalidate) throw new InvalidDataException("Empty scheduled event");
                state.Schedule.Enqueue(new(before, location, data, invalidate));
            }
        }
        if (root.TryGetProperty("writePermissions", out var permissions))
            foreach (var permission in permissions.EnumerateArray())
            {
                var start = ParseAddress(permission.GetProperty("address").GetString()!);
                var size = permission.GetProperty("size").GetInt32();
                if (size < 0) throw new InvalidDataException("Negative permission range size");
                var allowed = permission.GetProperty("allowed").GetBoolean();
                for (var i = 0; i < size; i++) state.WritePermissions.Add(unchecked(start + (ulong)i), allowed);
            }
        var executable = root.TryGetProperty("roundtrip", out var roundtrip) && roundtrip.GetBoolean() ? MirJson.Deserialize(MirJson.Serialize(lift.Ir)) : lift.Ir;
        var execution = MirInterpreter.Execute(executable, state);
        Console.WriteLine(JsonSerializer.Serialize(new
        {
            supported = true, length = bytes.Length, decoded, lift.Form, support = lift.Ir.Support.ToString(), operations = lift.Ir.Operations.Length,
            profile = lift.Ir.ProfileId, capabilities = DescribeContract(lift.Ir),
            slots = state.Slots.ToDictionary(k => k.Key, v => "0x" + v.Value.ToString("X")),
            memory = state.Memory.ToDictionary(k => $"0x{k.Key:X}", v => (int)v.Value), state.Accesses,
            events = state.Events,
            reservation = state.Reservation is { } saved ? new { address = $"0x{saved.Address:X}", sizeBytes = saved.SizeBytes } : null,
            exclusiveDecisions = state.ExclusiveStoreDecisions.ToArray(),
            appliedSchedule = state.AppliedSchedule, remainingSchedule = state.Schedule.ToArray(),
            execution.Outcome, next = execution.NextAddress is { } pc ? $"0x{pc:X}" : null, execution.Choices,
            execution.Event, resumeAddress = execution.ResumeAddress is { } resume ? $"0x{resume:X}" : null,
            stoppedOperation = execution.FaultOperation, completedStateToken = execution.CompletedStateToken.Id,
            stateKind = execution.StateKind.ToString(), choicePolicy = execution.ChoicePolicy.ToString(),
            stop = execution.Stop is { } stop ? new
            {
                kind = stop.Kind.ToString(), reason = stop.Reason, operationIndex = stop.OperationIndex,
                completedStateToken = stop.CompletedStateToken.Id, memoryEventStart = stop.MemoryEventStart, memoryEventCount = stop.MemoryEventCount
            } : null,
            exception = execution.Exception is { } boundary ? new
            {
                kind = boundary.Kind.ToString(), detail = boundary.Detail, savedAddress = $"0x{boundary.SavedAddress:X}", syndrome = boundary.Syndrome
            } : null,
            choiceObservations = state.ChoiceObservations.Select(choice => new
            {
                sequence = choice.Sequence, instructionAddress = $"0x{choice.InstructionAddress:X}", operationIndex = choice.OperationIndex,
                result = choice.Result, bits = "0x" + choice.Bits.ToString("X"), isExplicit = choice.IsExplicit
            }),
            remainingChoiceInputs = state.ChoiceInputs.Select(bits => "0x" + bits.ToString("X"))
        }));
    }
    return 0;
}
if (args.Length == 3 && args[0] == "scan")
{
    var image = ImageDocument.Load(args[1]);
    var report = CorpusScanner.Run(image, args[2]);
    Console.WriteLine(JsonSerializer.Serialize(report, MirJson.Options));
    return !report.StructuralChecksPassed ? 3 : !report.FullyLifted ? 2 : 0;
}
if (args.Length == 3 && args[0] == "lift")
{
    var image = ImageDocument.Load(args[1]);
    var address = ParseAddress(args[2]);
    var range = image.Ranges.Single(r => r.Executable && address >= r.Address && address - r.Address < r.FileSize);
    var offset = checked(range.FileOffset + (long)(address - range.Address));
    var length = (int)Math.Min(image.Architecture == Architecture.Arm64 ? 4UL : 15UL, range.FileSize - (address - range.Address));
    var bytes = image.Bytes.Slice((int)offset, length);
    if (image.Architecture == Architecture.X64)
    {
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes.ToArray()));
        decoder.IP = address;
        var instruction = decoder.Decode();
        bytes = bytes[..instruction.Length];
    }
    var lift = image.HasCodeRelocation(address, bytes.Length)
        ? LiftResult.Unsupported("code.relocation", "CodeRelocationRequired")
        : Lift(image.Architecture, new(image.Sha256, address, offset, bytes));
    if (lift.Ir is { } lifted)
    {
        var errors = MirValidator.Validate(lifted);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
    }
    Console.WriteLine(lift.Ir is { } ir ? MirJson.Serialize(ir) : JsonSerializer.Serialize(lift));
    return lift.IsSupported ? 0 : 2;
}
Console.Error.WriteLine("Cpp2CS: selftest | serve | validate-ir (stdin) | validate-nir (stdin) | scan <binary> <output-directory> | lift <binary> <image-va-hex> | native <binary> <entry-va-hex[,entry...]> <instruction-budget> <report.json> | native-check <arm64-binary> <x64-binary> <output-directory> | nir <binary> <contracts.json> <output-directory> | nir-check <arm64-binary> <x64-binary> <output-directory> | nir-aggregate-check <arm64-binary> <x64-binary> <inventory-directory> <output-directory> | nir-low-bits-check <x64-binary> <inventory-directory> <report.json> | nir-corpus <binary> <inventory.json> <output-directory> [instruction-budget] [diagnostic-budget] [normalization-rounds]");
return 1;

static LiftResult Lift(Architecture architecture, InstructionOrigin origin)
{
    if (architecture == Architecture.Arm64) return Arm64Lifter.Lift(origin);
    var decoder = Decoder.Create(64, new ByteArrayCodeReader(origin.Bytes.ToArray()));
    decoder.IP = origin.Address;
    var instruction = decoder.Decode();
    if (instruction.IsInvalid || instruction.Length != origin.Bytes.Length) return LiftResult.Unsupported("invalid", "invalid or multiple x64 instructions");
    return X64Lifter.Lift(origin, instruction);
}

static ulong ParseAddress(string text) => ulong.Parse(text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text, NumberStyles.HexNumber);
static BigInteger ParseBits(string text) => BigInteger.Parse("0" + (text.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ? text[2..] : text), NumberStyles.AllowHexSpecifier);

static object DescribeContract(MirInstruction ir)
{
    var capability = MirContracts.Capabilities(ir);
    return new
    {
        structuralRepresentation = true, support = capability.Support.ToString(),
        normalTransitionRepresented = capability.NormalTransitionRepresented,
        exceptionBoundaryRepresented = capability.ExceptionBoundaryRepresented,
        mayStopBeforeExit = capability.MayStopBeforeExit, hasChoices = capability.HasChoices,
        faultDeliveryModeled = capability.FaultDeliveryModeled, concurrentExecutionsVerified = capability.ConcurrentExecutionsVerified,
        obligations = capability.Obligations.Select(item => new { kind = item.Kind.ToString(), reason = item.Reason, operationIndex = item.OperationIndex }),
        finalStateToken = ir.FinalState.Id,
        meaning = "MIR contract only; no native or game equivalence claim"
    };
}
