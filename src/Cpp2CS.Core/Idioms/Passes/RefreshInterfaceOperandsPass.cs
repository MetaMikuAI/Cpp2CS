using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RefreshInterfaceOperandsPass
{
    internal static void RefreshInterfaceOperands(this IdiomState state)
    {
        var updated = new Dictionary<Variable, (object?, int)>();
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Op: { Kind: OpKind.InterfaceInvokeData, Operand: ValueTuple<object?, int> { Item1: null } pair } } data && data.Arguments.Length > 1 && state.defs.Expand(data.Arguments[1]) is Symbol { Kind: SymbolKind.Class } itf && data.Defines is [var result])
                {
                    var operand = ((object?)itf.Value, pair.Item2);
                    block.Statements[i] = data with
                    {
                        Op = new RuntimeOp(OpKind.InterfaceInvokeData, operand)
                    };
                    state.interfaceData[result] = operand;
                    updated[result] = operand;
                }

        if (updated.Count == 0)
            return;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is Call { Op: { Kind: OpKind.CallInterface, Operand: ValueTuple<object?, int> { Item1: null } } } call && state.defs.Expand(call.Target) is Load { Address: var address } && SplitPass.Split(address) is (Use { Variable: var data }, 0) && updated.TryGetValue(data, out var operand))
                    block.Statements[i] = call with
                    {
                        Op = new RuntimeOp(OpKind.CallInterface, operand)
                    };
    }
}
