using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ReplacePass
{
    internal static Func<Expr, Expr?> Replace(Expr load, ulong value) => e => e == load ? Expr.C(value, e.Width) : null;
}
