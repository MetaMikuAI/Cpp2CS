using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed record VirtualDelegate(Expr Receiver, int Slot, HashSet<Variable> Metadata);
