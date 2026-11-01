using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class CountCallsPass
{
    internal static void CountCalls(this IdiomState state)
    {
        foreach (var call in state.All.OfType<Call>())
        {
            if (state.owner.HelperOf(call) is { } helper)
                state.Result.HelperCalls[helper.Kind] = state.Result.HelperCalls.GetValueOrDefault(helper.Kind) + 1;
            else if (call.Kind is CallKind.Indirect or CallKind.TailIndirect)
                state.Result.IndirectCalls++;
        }
    }
}
