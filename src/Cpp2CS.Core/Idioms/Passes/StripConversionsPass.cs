using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class StripConversionsPass
{
    internal static Expr StripConversions(Expr e) => e is Ir.Convert c ? StripConversionsPass.StripConversions(c.Operand) : e is Extract { Low: 0 } x ? StripConversionsPass.StripConversions(x.Operand) : e;
}
