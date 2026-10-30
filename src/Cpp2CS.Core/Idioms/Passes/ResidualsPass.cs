using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ResidualsPass
{
    internal static void Residuals(this IdiomState state)
    {
        foreach (var block in state.function.Blocks)
            foreach (var stmt in block.Statements)
            {
                if (stmt is Call { Op: null } call)
                {
                    if (state.owner.HelperOf(call) is { } helper)
                        state.Result.Residuals.Add(new(call.Address, $"helper:{helper}", DescribePass.Describe(call)));
                    else if (call.Kind is CallKind.Indirect or CallKind.TailIndirect)
                        state.Result.Residuals.Add(new(call.Address, $"indirect:{ShapePass.Shape(state.defs.Expand(call.Target))}", DescribePass.Describe(call)));
                    else if (call.Target is Const target && state.facts.Code.RegionOf(target.Value) == CodeRegion.Managed && state.facts.EntriesAt(target.Value).Length == 0)
                    {
                        var identity = state.facts.Unregistered.At(target.Value);
                        if (identity is null)
                            state.Result.Residuals.Add(new(call.Address, "call:unregistered-managed", DescribePass.Describe(call)));
                        else if (UnregisteredMethods.Resolve(identity, call, e => state.defs.Expand(e), state.owner.abi, out var reason) is null)
                            state.Result.Residuals.Add(new(call.Address, $"call:unregistered-managed:{reason}", DescribePass.Describe(call)));
                    }
                }

                foreach (var load in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Load>())
                    if (TermsPass.Terms(load.Address) is [Symbol { Kind: SymbolKind.Class or SymbolKind.Method or SymbolKind.Field } symbol, Const offset])
                        state.Result.Residuals.Add(new(stmt.Address, $"load:{symbol.Kind}+0x{offset.Value:x}", stmt.ToString()));
            }

        foreach (var slot in state.Result.ReadSlots.Except(state.Result.InitializedSlots))
            state.Result.Residuals.Add(new(state.function.Entry, $"slot-read-without-init:{state.facts.Usages.At(slot)!.Usage.Kind}", $"0x{slot:x} {state.facts.Usages.At(slot)!.Usage}"));
    }
}
