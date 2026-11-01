using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomState;

namespace Cpp2CS.Idioms;

internal static class PlacementPass
{
    internal static object? Placement(this IdiomState state, Expr expanded, Block head, Point start)
    {
        var stripped = StripConversionsPass.StripConversions(expanded);
        // 读取优先按"基址 + 偏移"布置：模板可能重新读取内存，寄存器里同一表达式的旧值不一定被用到
        var registers = state.Location(expanded, head, start) ?? state.Location(stripped, head, start);
        if (stripped is Load load && SplitPass.Split(load.Address) is var (basis, offset) && state.Location(basis, head, start) is { } at)
        {
            // 同时给出展开相同的寄存器：模板用的可能是早先读到寄存器里的值，也可能重新读内存
            var field = new Dictionary<string, object>
            {
                ["base"] = at,
                ["offset"] = offset,
                ["width"] = load.Width
            };
            if (registers is not null)
                field["also"] = registers;
            return field;
        }

        return registers;
    }
}
