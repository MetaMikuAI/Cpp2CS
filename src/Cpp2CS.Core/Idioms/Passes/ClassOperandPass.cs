using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ClassOperandPass
{
    internal static object? ClassOperand(this IdiomState state, IEnumerable<Expr> arguments) => arguments.Select(a => state.defs.Expand(a)).OfType<Symbol>().FirstOrDefault(s => s.Kind == SymbolKind.Class)?.Value;
}
