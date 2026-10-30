using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomState;

namespace Cpp2CS.Idioms;

internal static class LocationPass
{
    internal static string? Location(this IdiomState state, Expr expanded, Block head, Point start)
    {
        var places = new List<string>();
        if (expanded is Symbol symbol && state.symbolSlots.TryGetValue(symbol, out var slot))
            places.Add($"slot:0x{slot:x}");
        // 删去的槽位读取没有经过符号化，仍是对槽位地址的读取
        var slotLoad = places.Count > 0 ? new Load(Expr.C(state.symbolSlots[(Symbol)expanded], 64), 64) : null;
        for (var i = 0; i < 31; i++)
            if (state.ReachingBefore(head, start, Storage.Gpr(i)) is { } v && state.defs.Expand(new Use(v, 64)) is var e && (e == expanded || e == slotLoad))
                places.Add($"x{i}");
        return places.Count == 0 ? null : string.Join("+", places);
    }
}
