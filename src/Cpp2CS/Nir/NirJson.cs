using System.Globalization;
using System.Numerics;
using System.Text.Json;
using System.Text.Json.Serialization;

namespace Cpp2CS.Nir;

public static class NirJson
{
    private static readonly JsonSerializerOptions Options = CreateOptions();
    public static string Serialize(NirModule module) => JsonSerializer.Serialize(module, Options);
    public static NirModule Deserialize(string json) => JsonSerializer.Deserialize<NirModule>(json, Options)
        ?? throw new JsonException("NIR module cannot be null");
    private static JsonSerializerOptions CreateOptions()
    {
        var result = new JsonSerializerOptions
        {
            PropertyNamingPolicy = JsonNamingPolicy.CamelCase, WriteIndented = true,
            UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow, RespectNullableAnnotations = true,
            RespectRequiredConstructorParameters = true, AllowDuplicateProperties = false
        };
        result.Converters.Add(new BigIntegerConverter());
        result.Converters.Add(new JsonStringEnumConverter());
        return result;
    }
    private sealed class BigIntegerConverter : JsonConverter<BigInteger>
    {
        public override BigInteger Read(ref Utf8JsonReader reader, Type typeToConvert, JsonSerializerOptions options)
        {
            if (reader.TokenType != JsonTokenType.String || !BigInteger.TryParse(reader.GetString(), NumberStyles.Integer, CultureInfo.InvariantCulture, out var value))
                throw new JsonException("NIR bit patterns and addresses use decimal strings");
            return value;
        }
        public override void Write(Utf8JsonWriter writer, BigInteger value, JsonSerializerOptions options) => writer.WriteStringValue(value.ToString(CultureInfo.InvariantCulture));
    }
}
