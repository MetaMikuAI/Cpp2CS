using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RefreshOperandsPass
{
    internal static void RefreshOperands(this IdiomState state)
    {
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is Call call)
                    block.Statements[i] = Refresh(call, e => state.defs.Expand(e));
            }
    }

    internal static Call Refresh(Call call, Func<Expr, Expr> expand) =>
        call.Op is { Operand: null, Kind: OpKind.InitClass or OpKind.RunClassConstructor or OpKind.NewObject or OpKind.NewArray or OpKind.Box or OpKind.Unbox or OpKind.IsInst } op
            && call.Arguments.Select(expand).OfType<Symbol>().FirstOrDefault(s => s.Kind == SymbolKind.Class)?.Value is { } type
            ? call with { Op = op with { Operand = type } } : call;
}
