using Cpp2CS;
using Cpp2CS.Arm64;
using Cpp2CS.Images;
using Cpp2CS.Ir;
using Cpp2CS.Validation;
using Cpp2CS.X64;
using Iced.Intel;
using System.Globalization;
using System.Numerics;
using System.Text.Json;

if (args.Length == 1 && args[0] == "selftest") return CoreChecks.Run();
if (args.Length == 1 && args[0] == "validate-ir")
{
    Console.WriteLine(MirJson.Serialize(MirJson.Deserialize(Console.In.ReadToEnd())));
    return 0;
}
if (args.Length == 1 && args[0] == "serve")
{
    while (Console.ReadLine() is { } line)
    {
        using var input = JsonDocument.Parse(line);
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
            Console.WriteLine(JsonSerializer.Serialize(new { supported = true, length = bytes.Length, decoded, lift.Form, support = lift.Ir.Support.ToString(), operations = lift.Ir.Operations.Count }));
            continue;
        }
        var state = new MachineState();
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
            supported = true, length = bytes.Length, decoded, lift.Form, support = lift.Ir.Support.ToString(), operations = lift.Ir.Operations.Count,
            slots = state.Slots.ToDictionary(k => k.Key, v => "0x" + v.Value.ToString("X")),
            memory = state.Memory.ToDictionary(k => $"0x{k.Key:X}", v => (int)v.Value), state.Accesses,
            events = state.Events,
            reservation = state.Reservation is { } saved ? new { address = $"0x{saved.Address:X}", sizeBytes = saved.SizeBytes } : null,
            exclusiveDecisions = state.ExclusiveStoreDecisions.ToArray(),
            appliedSchedule = state.AppliedSchedule, remainingSchedule = state.Schedule.ToArray(),
            execution.Outcome, next = execution.NextAddress is { } pc ? $"0x{pc:X}" : null, execution.Choices,
            execution.Event, resumeAddress = execution.ResumeAddress is { } resume ? $"0x{resume:X}" : null
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
Console.Error.WriteLine("Cpp2CS: selftest | serve | validate-ir (stdin) | scan <binary> <output-directory> | lift <binary> <image-va-hex>");
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
