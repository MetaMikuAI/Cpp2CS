using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

/// <summary>共享泛型运行时模板；外部调用必须由导出身份、导入名或完整子模板确认。</summary>
internal static class SharedRuntimeHelpers
{
    private static bool Match(ProgramFacts facts, ulong address, uint[] words, params (int Offset, bool Tail, Func<ulong, bool> Accept)[] calls)
    {
        if (facts.Code.At(address) is not { } function || function.Start != address || function.Size != (ulong)words.Length * 4) return false;
        for (var i = 0; i < words.Length; i++)
            if (words[i] != 0 && facts.Code.Word(address + (uint)i * 4) != words[i]) return false;
        foreach (var (offset, tail, accept) in calls)
        {
            var pc = address + (uint)offset;
            if (facts.Code.Word(pc) is not { } word || !(tail ? A64.IsB(word) : A64.IsBl(word)) || !accept(A64.Imm26Target(word, pc))) return false;
        }
        return true;
    }

    internal static bool UnboxAny(ProgramFacts facts, ulong address)
    {
        bool Kind(ulong target, HelperKind kind, string? detail = null) => facts.Helpers.InternalCall(target) is var helper
            && helper.Kind == kind && (detail is null || helper.Detail == detail);
        // 引用类型检查并写入临时槽；普通值类型检查后返回对象数据；Nullable 使用独立复制模板。
        return Match(facts, address,
        [
            0xa9be57fe, 0xa9014ff4, 0xb9402828, 0xaa0203f5, 0xaa0103f3, 0xaa0003f4, 0x37f800e8, 0xb4000294,
            0xaa1403e0, 0xaa1303e1, 0, 0xb5000220, 0x1400001f, 0xf9403268, 0xb4000068, 0x3944d668,
            0x37180228, 0xb40003b4, 0xf9400288, 0xf9402269, 0xf9402108, 0xeb09011f, 0x540002a1, 0xaa1403e0,
            0xa9414ff4, 0xa8c257fe, 0, 0xaa1f03e0, 0xf90002a0, 0xa9414ff4, 0xaa1503e0, 0xa8c257fe,
            0xd65f03c0, 0xb40000b4, 0xf9400288, 0xf9402261, 0xeb01011f, 0x54000141, 0xaa1403e0, 0xaa1303e1,
            0xaa1503e2, 0, 0x17fffff3, 0xaa1403e0, 0xaa1303e1, 0, 0, 0xaa1403e0, 0,
        ], (0x28, false, t => Kind(t, HelperKind.IsInst)), (0x68, true, t => Kind(t, HelperKind.Unbox)),
            (0xa4, false, t => NullableUnbox(facts, t)), (0xb4, false, t => Kind(t, HelperKind.Throw, "System.InvalidCastException")),
            (0xb8, false, t => Kind(t, HelperKind.Throw, "System.NullReferenceException")), (0xc0, false, t => Kind(t, HelperKind.Throw, "System.InvalidCastException")));
    }

    private static bool NullableUnbox(ProgramFacts facts, ulong address) => Match(facts, address,
    [
        0xa9be57fe, 0xa9014ff4, 0xf9404028, 0xaa0103f5, 0xaa0003f4, 0xaa0203e0, 0x91008101, 0xaa0203f3,
        0, 0xf94022a8, 0xb940f908, 0x51004108, 0xb40000d4, 0x91004281, 0x2a0803e2, 0,
        0x52800028, 0x14000005, 0x2a0803e2, 0x2a1f03e1, 0, 0x2a1f03e8, 0x39000268, 0xa9414ff4, 0xa8c257fe, 0xd65f03c0,
    ], (0x20, false, t => facts.Helpers.InternalCall(t).Kind == HelperKind.FieldAddress),
        (0x3c, false, t => facts.Helpers.InternalCall(t) is { Kind: HelperKind.Import, Detail: "memcpy" }),
        (0x50, false, t => facts.Helpers.InternalCall(t) is { Kind: HelperKind.Import, Detail: "memset" }));

    internal static bool ConstrainedInvoke(ProgramFacts facts, ulong address) => Match(facts, address,
    [
        0xa9bd5ffe, 0xa90157f6, 0xa9024ff4, 0xb9402808, 0xaa0503f3, 0xaa0403f4, 0xaa0303f6, 0xaa0103f5,
        0x37f80148, 0xf94002d6, 0xb4000736, 0xaa1603e0, 0xaa1503e1, 0, 0xaa0003e1, 0xa9409400,
        0xaa1603e2, 0x14000012, 0xf94012a8, 0xeb00011f, 0x540002a0, 0x39446109, 0x372800c9, 0x3940a908,
        0x7100791f, 0x54000060, 0x71004d1f, 0x540002a1, 0xaa1603e1, 0, 0xf94002a8, 0xf9400aa5,
        0xaa0003e2, 0xaa1503e1, 0xaa0803e0, 0xaa1403e3, 0xaa1303e4, 0xa9424ff4, 0xa94157f6, 0xa8c35ffe,
        0xd61f00a0, 0xb940e008, 0x35000048, 0, 0xf9400aa5, 0xf94002a0, 0xaa1503e1, 0x17ffffe1,
        0xf9403008, 0xaa0203f7, 0xb40000c8, 0x3944d408, 0x36180088, 0x394002c8, 0x340001a8, 0xf9402000,
        0x92800008, 0xa90022e0, 0xb940fc02, 0x910042e0, 0xaa1603e1, 0, 0xf9400aa5, 0xf94002a0,
        0xaa1503e1, 0xaa1703e2, 0x17ffffe1, 0,
    ], (0x34, false, t => facts.Helpers.InternalCall(t).Kind == HelperKind.VirtualMethodLookup),
        (0x74, false, t => facts.Helpers.InternalCall(t).Kind == HelperKind.Box),
        (0xac, false, t => facts.Helpers.InternalCall(t).Kind == HelperKind.ClassInit),
        (0xf4, false, t => facts.Helpers.InternalCall(t) is { Kind: HelperKind.Import, Detail: "memcpy" }),
        (0x10c, false, t => facts.Helpers.InternalCall(t) is { Kind: HelperKind.Throw, Detail: "System.NullReferenceException" }));
}
