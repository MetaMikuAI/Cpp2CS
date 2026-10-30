using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RefreshOperandsPass
{
    internal static void RefreshOperands(this IdiomState state)
    {
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: { Operand: null, Kind: OpKind.InitClass or OpKind.RunClassConstructor or OpKind.NewObject or OpKind.NewArray or OpKind.Box or OpKind.Unbox or OpKind.IsInst } op } call)
                    continue;
                if (state.ClassOperand(call.Arguments) is { } type)
                    block.Statements[i] = call with
                    {
                        Op = op with
                        {
                            Operand = type
                        }
                    };
            }
    }
}
