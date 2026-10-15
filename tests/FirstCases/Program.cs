using System.Text.Json;
using Sekai;
using Sekai.Api;
using Sekai.Mysekai;

var oracle = JsonDocument.Parse(File.ReadAllText(args[0])).RootElement;
int assertions = 0;
void Check(bool condition, string label)
{
    assertions++;
    if (!condition) throw new InvalidOperationException(label);
}
int[] Triple(StaminaData value) => [value.normal, value.enhance, value.boost];
int[] Numbers(JsonElement value) => value.EnumerateArray().Select(n => n.GetInt32()).ToArray();
Check(oracle.GetProperty("binarySha256").GetString() == "6CE1DE5C0357E122F153F62D648DE1655B7F8A339B2AE1C575595868A361E4BB", "input hash");
foreach (var row in oracle.GetProperty("stamina").EnumerateArray())
{
    var a = Numbers(row.GetProperty("a")); var b = Numbers(row.GetProperty("b"));
    var left = new StaminaData(a[0], a[1], a[2]); var right = new StaminaData(b[0], b[1], b[2]);
    Check(Triple(left).SequenceEqual(Numbers(row.GetProperty("constructed"))), "constructor");
    Check(left.IsHasBoostStaminaOrEnhanceStamina == row.GetProperty("has").GetBoolean(), "has");
    Check(left.IsEmptyStamina == row.GetProperty("empty").GetBoolean(), "empty");
    Check(left.SumStamina == row.GetProperty("sum").GetInt32(), "sum");
    Check(Triple(left + right).SequenceEqual(Numbers(row.GetProperty("add"))), "add");
    Check(Triple(left - right).SequenceEqual(Numbers(row.GetProperty("sub"))), "subtract");
    Check(Triple(left).SequenceEqual(a) && Triple(right).SequenceEqual(b), "value arguments unchanged");
}
Check(Triple(StaminaData.Zero).SequenceEqual(Numbers(oracle.GetProperty("zero"))), "zero");
foreach (var row in oracle.GetProperty("requests").EnumerateArray())
{
    var input = Numbers(row.GetProperty("input"));
    var value = new MusicScoreSearchConditionRequest(input[0], input[1], (MusicDifficulty)input[2], (CustomMusicScoreSearchDisplayOrderCategory)input[3]);
    int[] actual = [value.MusicId, value.MusicScoreTagId, (int)value.Difficulty, (int)value.DisplayOrderCategory];
    Check(actual.SequenceEqual(Numbers(row.GetProperty("fields"))), "request fields");
}
var defaults = new MusicScoreSearchConditionRequest();
Check(defaults.MusicId == -1 && defaults.MusicScoreTagId == -1 && defaults.Difficulty == MusicDifficulty.none && defaults.DisplayOrderCategory == CustomMusicScoreSearchDisplayOrderCategory.popular, "metadata defaults");
Check(typeof(MusicScoreSearchConditionRequest).GetFields().All(f => f.IsInitOnly), "readonly contract");
Check(System.Runtime.InteropServices.Marshal.SizeOf<StaminaData>() == 12, "struct layout");
File.WriteAllText(Path.Combine(Path.GetDirectoryName(Path.GetFullPath(args[0]))!, "verification.json"), JsonSerializer.Serialize(new
{
    passed = true, assertions, completeTypes = 2, methods = 8,
    staminaCases = oracle.GetProperty("stamina").GetArrayLength(),
    requestCases = oracle.GetProperty("requests").GetArrayLength(),
    nativeCalls = oracle.GetProperty("nativeCalls").GetInt32(),
    gameRuntimeVerified = false,
    oracleSha256 = Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(args[0])))
}, new JsonSerializerOptions { WriteIndented = true }));
Console.WriteLine($"PASS: {assertions} assertions; 2 complete types / 8 methods; native differential execution, checked caller");
