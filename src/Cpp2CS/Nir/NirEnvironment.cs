using System.Numerics;

namespace Cpp2CS.Nir;

public enum NirEnvironmentField
{
    RoundingMode, FlushSubnormalInput, FlushSubnormalOutput, CanonicalNaN,
    // 六位依次为无效、除零、溢出、下溢、不精确、非正规输入；TrapMask 的 1 表示启用陷阱。
    FloatingExceptions, FloatingTrapMask
}

public sealed record NirEnvironmentRead(NirValue Result, NirEnvironmentField Field, NirEffectFlow Flow) : NirOperation;
public sealed record NirEnvironmentWrite(NirEnvironmentField Field, NirValue Value, NirEffectFlow Flow) : NirOperation;
public sealed record NirEnvironmentResult(BigInteger Value, string? Error = null)
{
    public bool Success => Error is null;
}

public static class NirEnvironmentContract
{
    public static int Width(NirEnvironmentField field) => field switch
    {
        NirEnvironmentField.RoundingMode => 3,
        NirEnvironmentField.FlushSubnormalInput or NirEnvironmentField.FlushSubnormalOutput or NirEnvironmentField.CanonicalNaN => 1,
        NirEnvironmentField.FloatingExceptions or NirEnvironmentField.FloatingTrapMask => 6,
        _ => 0
    };

    public static bool Valid(NirEnvironmentField field, BigInteger value) =>
        Width(field) is > 0 and var width && value >= 0 && value < (BigInteger.One << width) &&
        (field != NirEnvironmentField.RoundingMode || value <= 4);
}
