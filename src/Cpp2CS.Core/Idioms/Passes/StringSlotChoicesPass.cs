using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class StringSlotChoicesPass
{
    internal static bool StringSlotChoices(this IdiomState state)
    {
        var definitions = new Defs(state.function);
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, part =>
                {
                    if (part is not Load { Width: 64 } load)
                        return null;
                    var address = load.Address;
                    for (var depth = 0; depth < 8 && address is Use use && definitions.Raw(use.Variable) is { } value; depth++)
                        address = value;
                    if (address is not Select || state.SlotValue(definitions.Expand(address), out var slots) is not { } choice || slots.Any(s => s.Usage.Kind != UsageKind.StringLiteral))
                        return null;
                    changed = true;
                    state.Result.ReadSlots.UnionWith(slots.Select(s => s.Address));
                    return choice;
                }));
        return changed;
    }
}
