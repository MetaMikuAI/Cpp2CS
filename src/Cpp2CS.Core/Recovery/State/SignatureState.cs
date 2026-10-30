using Cpp2CS.Facts;
using Cpp2CS.Ir;
using static Cpp2CS.Recovery.MethodRecovery;

namespace Cpp2CS.Recovery;

internal sealed class SignatureState
{
    internal readonly Dictionary<Storage, Argument> arguments = new();
    internal RecoveryHole? returnHole;
    internal TypeRef returnType = null!;
    internal readonly Dictionary<Storage, ArgumentValue> sharedIncoming = [];
    internal readonly Dictionary<Storage, ManagedValue> indirectRoots = new();
    internal LocalValue? ownReturnBuffer;
    internal readonly Dictionary<Storage, (ArgumentValue Root, AbiPiece Piece)> structArguments = new();
}
