using System.Collections.Frozen;

namespace Cpp2CS.Ir;

public static class StateLayout
{
    public static IReadOnlyDictionary<string, int> For(Architecture architecture) => architecture switch
    {
        Architecture.Arm64 => Arm, Architecture.X64 => X64,
        _ => throw new ArgumentOutOfRangeException(nameof(architecture))
    };

    private static readonly FrozenDictionary<string, int> Arm = CreateArm().ToFrozenDictionary(StringComparer.Ordinal);
    private static readonly FrozenDictionary<string, int> X64 = CreateX64().ToFrozenDictionary(StringComparer.Ordinal);

    private static Dictionary<string, int> CreateArm()
    {
        var slots = new Dictionary<string, int> { ["sp"] = 64, ["n"] = 1, ["z"] = 1, ["c"] = 1, ["v"] = 1, ["fpcr"] = 32, ["fpsr"] = 32 };
        for (var i = 0; i < 31; i++) slots.Add($"x{i}", 64);
        for (var i = 0; i < 32; i++) slots.Add($"v{i}", 128);
        slots.Add("tpidr_el0", 64);
        slots.Add("apia_key", 128);
        slots.Add("apib_key", 128);
        slots.Add("pauth_ia_enabled", 1);
        slots.Add("pauth_ib_enabled", 1);
        slots.Add("btype", 2);
        slots.Add("bti_bt0", 1);
        return slots;
    }

    private static Dictionary<string, int> CreateX64()
    {
        var slots = new Dictionary<string, int>();
        foreach (var name in new[] { "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "fsbase", "gsbase" }) slots.Add(name, 64);
        foreach (var name in new[] { "cf", "pf", "af", "zf", "sf", "of", "df" }) slots.Add(name, 1);
        foreach (var name in new[] { "cs", "es", "ss", "ds", "fs", "gs" }) slots.Add(name, 16);
        for (var i = 0; i < 16; i++) slots.Add($"xmm{i}", 128);
        for (var i = 0; i < 16; i++) slots.Add($"ymm{i}_hi", 128);
        slots.Add("mxcsr", 32);
        return slots;
    }
}
