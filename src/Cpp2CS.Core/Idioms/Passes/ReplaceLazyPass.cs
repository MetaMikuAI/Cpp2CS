using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class ReplaceLazyPass
{
    internal static void ReplaceLazy(this IdiomState state)
    {
        var calls = new Dictionary<Call, Symbol>(ReferenceEqualityComparer.Instance);
        foreach (var (call, symbol) in state.lazyValues)
            calls[call] = symbol;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || !calls.TryGetValue(call, out var value))
                    continue;
                if (call.Defines.FirstOrDefault() is { } result)
                    block.Statements[i] = new Define(call.Address, result, value);
                else
                    block.Statements[i] = new Nop(call.Address, "InitMetadata");
            }

        state.Result.Errors.AddRange(Lowering.Cleanup(state.function));
        state.defs = new Defs(state.function);
    }
}
