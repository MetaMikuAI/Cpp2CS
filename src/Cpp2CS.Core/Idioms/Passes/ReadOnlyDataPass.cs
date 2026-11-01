
namespace Cpp2CS.Idioms;

internal static class ReadOnlyDataPass
{
    internal static void ReadOnlyData(this IdiomState state)
    {
        if (!ReadOnlyDataNormalizer.Run(state.function, state.facts.Model.Image, address => state.facts.Usages.At(address)?.Usage.Kind is UsageKind.StringLiteral or UsageKind.MethodDef or UsageKind.MethodRef))
            return;
        state.Cleanup();
        if (state.MetadataSlotPhis())
            state.Cleanup();
        if (state.StringSlotChoices())
            state.Cleanup();
    }
}
