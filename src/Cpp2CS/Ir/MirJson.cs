using System.Globalization;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Cpp2CS.Ir;

public static class MirJson
{
    public const string SchemaVersion = "cpp2cs.mir/0.1";
    public const string SemanticsVersion = "attempt08-integer-1";
    public static readonly JsonSerializerOptions Options = CreateOptions();

    private static JsonSerializerOptions CreateOptions()
    {
        var options = new JsonSerializerOptions { WriteIndented = false };
        options.Converters.Add(new JsonStringEnumConverter());
        options.Converters.Add(new BigIntegerHexConverter());
        options.Converters.Add(new UInt64HexConverter());
        return options;
    }

    public static string Serialize(MirInstruction ir)
    {
        var errors = MirValidator.Validate(ir);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return JsonSerializer.Serialize(new MirEnvelope(SchemaVersion, SemanticsVersion, MachineProfile.For(ir.Architecture).Id, ir), Options);
    }
    public static MirInstruction Deserialize(string json)
    {
        var envelope = JsonSerializer.Deserialize<MirEnvelope>(json, Options) ?? throw new InvalidDataException("Missing MIR envelope");
        if (envelope.Schema != SchemaVersion || envelope.Semantics != SemanticsVersion) throw new InvalidDataException("Unsupported MIR schema or semantics");
        if (envelope.Profile != MachineProfile.For(envelope.Instruction.Architecture).Id) throw new InvalidDataException("Unsupported MIR profile");
        var errors = MirValidator.Validate(envelope.Instruction);
        if (errors.Count != 0) throw new InvalidDataException(string.Join("; ", errors));
        return envelope.Instruction;
    }

    private sealed record MirEnvelope(string Schema, string Semantics, string Profile, MirInstruction Instruction);

    private sealed class BigIntegerHexConverter : JsonConverter<BigInteger>
    {
        public override BigInteger Read(ref Utf8JsonReader reader, Type type, JsonSerializerOptions options) => BigInteger.Parse("0" + HexDigits(reader.GetString()), NumberStyles.AllowHexSpecifier);
        public override void Write(Utf8JsonWriter writer, BigInteger value, JsonSerializerOptions options)
        {
            if (value.Sign < 0) throw new InvalidDataException("MIR immediate must be unsigned");
            writer.WriteStringValue("0x" + value.ToString("X"));
        }
    }
    private sealed class UInt64HexConverter : JsonConverter<ulong>
    {
        public override ulong Read(ref Utf8JsonReader reader, Type type, JsonSerializerOptions options) => ulong.Parse(HexDigits(reader.GetString()), NumberStyles.HexNumber);
        public override void Write(Utf8JsonWriter writer, ulong value, JsonSerializerOptions options) => writer.WriteStringValue($"0x{value:X}");
    }

    private static string HexDigits(string? text)
    {
        if (text is null || !text.StartsWith("0x", StringComparison.Ordinal) || text.Length == 2 || !text.AsSpan(2).ContainsOnlyHexDigits())
            throw new InvalidDataException("Expected unsigned 0x-prefixed hexadecimal digits");
        return text[2..];
    }

    private static bool ContainsOnlyHexDigits(this ReadOnlySpan<char> text)
    {
        foreach (var character in text)
            if (!char.IsAsciiHexDigit(character)) return false;
        return true;
    }
}
