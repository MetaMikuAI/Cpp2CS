using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed record ArraySpan(Expr Array, Expr Start, MethodRef Factory);
