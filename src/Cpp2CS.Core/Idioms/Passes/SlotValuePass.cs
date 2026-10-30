using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class SlotValuePass
{
    internal static Expr? SlotValue(this IdiomState state, Expr address, out UsageSlot[] slots)
    {
        var found = new List<UsageSlot>();
        Expr? Read(Expr value)
        {
            if (value is Const constant && state.facts.Usages.At(constant.Value) is { } slot && slot.Usage.Kind is UsageKind.StringLiteral or UsageKind.MethodDef or UsageKind.MethodRef)
            {
                found.Add(slot);
                return new Symbol(SymbolOfPass.SymbolOf(slot.Usage.Kind), slot.Usage.Value);
            }

            return value is Select choice && Read(choice.True) is { } yes && Read(choice.False) is { } no ? choice with
            {
                True = yes,
                False = no
            }

            : null;
        }

        var result = Read(address);
        slots = found.ToArray();
        return slots.Select(s => SymbolOfPass.SymbolOf(s.Usage.Kind)).Distinct().Count() == 1 ? result : null;
    }
}
