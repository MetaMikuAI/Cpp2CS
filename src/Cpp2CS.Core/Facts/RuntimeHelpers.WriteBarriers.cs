using System.Collections.Concurrent;

namespace Cpp2CS.Facts;

public sealed partial class RuntimeHelpers
{
    private readonly ConcurrentDictionary<ulong, bool> notificationBarriers = new();

    /// <summary>GC 位图通知只标记地址所在页，不读取或写入该地址中的引用。</summary>
    public bool IsNotificationOnlyBarrier(ulong address) => notificationBarriers.GetOrAdd(address, entry =>
    {
        if (InternalCall(entry).Kind != HelperKind.WriteBarrier) return false;
        // il2cpp_codegen_write_barrier_for_class(klass, ptr)：丢弃 klass，把位置移到 x0 后进入同一个实现。
        if (map.Word(entry) == 0xaa0103e0 && map.Word(entry + 4) is { } forward && A64.IsB(forward)) entry = A64.Imm26Target(forward, entry + 4);
        // 只穿过不改变参数、无其他操作的直接跳板。
        for (var hop = 0; hop < 6; hop++)
        {
            if (map.Word(entry) is not { } first) return false;
            if (!A64.IsB(first)) return CardMarkingBody(Enumerable.Range(0, 18).Select(i => map.Word(entry + (uint)i * 4) ?? 0).ToArray());
            entry = A64.Imm26Target(first, entry);
        }
        return false;
    });

    /// <summary>开关关闭则返回；否则对全局位图执行原子的 OR。入口地址只用于计算页号和位号。</summary>
    internal static bool CardMarkingBody(IReadOnlyList<uint> w) => w.Count == 18
        && (w[0] & 0x9f00001f) == 0x90000008 // adrp x8, flag page
        && (w[1] & 0xffc003ff) == 0xb9400108 // ldr w8, [x8, flag offset]
        && w[2] == 0x340001e8 // cbz w8, ret
        && (w[3] & 0x9f00001f) == 0x9000000a // adrp x10, bitmap page
        && w[4] == 0xd3528008 // ubfx x8, x0, 18, 15
        && (w[5] & 0xffc003ff) == 0x9100014a // add x10, x10, bitmap offset
        && (w[6] & 0xffe0001f) == 0x5280000b // movz w11, low offset
        && w[7] == 0xd34cfc09 // lsr x9, x0, 12
        && (w[8] & 0xffe0001f) == 0x72a0000b // movk w11, high offset
        && w[9] == 0x5280002c // mov w12, 1
        && w[10] == 0x8b080d48 // add x8, x10, x8, lsl 3
        && w[11] == 0x8b0b0108 // add x8, x8, x11
        && w[12] == 0x9ac92189 // lsl x9, x12, x9
        && w[13] == 0xc85f7d0a // ldxr x10, [x8]
        && w[14] == 0xaa09014a // orr x10, x10, x9
        && w[15] == 0xc80b7d0a // stxr w11, x10, [x8]
        && w[16] == 0x35ffffab // cbnz w11, retry
        && w[17] == 0xd65f03c0;
}
