namespace Cpp2CS.Abi;

// 指令写入与 ABI 传值不同：前者定义物理寄存器，后者仅保证 ABI 指定的位。
public static class Arm64Registers
{
    public static string Canonical(string register) => register.ToLowerInvariant() switch
    {
        "fp" => "x29", "lr" => "x30", "wsp" => "sp",
        var r when r.Length > 1 && r[0] == 'w' => "x" + r[1..],
        var r when r.Length > 1 && r[0] is 's' or 'd' or 'q' && int.TryParse(r.AsSpan(1), out _) => "v" + r[1..],
        var r => r
    };
    public static int Width(string register) => register.ToLowerInvariant() switch
    {
        "memory" => 0, "nzcv" => 4, "sp" => 64, "wsp" => 32,
        var r when r[0] is 'w' or 's' => 32,
        var r when r[0] is 'v' or 'q' => 128, _ => 64
    };
    public static bool Zero(string register) => register is "xzr" or "wzr";
    public static readonly string[] CallWrites = [.. Enumerable.Range(0, 19).Append(30).Select(n => $"x{n}"),
        .. Enumerable.Range(0, 32).Select(n => $"v{n}"), "nzcv", "memory"];
    public static readonly string[] CallInputs = [.. Enumerable.Range(0, 9).Select(n => $"x{n}"),
        .. Enumerable.Range(0, 8).Select(n => $"v{n}"), "sp"];
    public static int PreservedByCall(string register)
    {
        register = Canonical(register);
        if (register.StartsWith('v') && int.TryParse(register.AsSpan(1), out var n) && n is >= 8 and <= 15) return 64;
        return CallWrites.Contains(register) ? 0 : Width(register);
    }
}
