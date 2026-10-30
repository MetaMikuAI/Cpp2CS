using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class ForwardedStructArgument
{
    internal static bool Whole(AbiValue parameter, IReadOnlyDictionary<Storage, Expr> registers,
        Func<Expr, (ArgumentValue Root, AbiPiece Piece)?> input)
    {
        if (parameter.Passing != Passing.Registers || parameter.Pieces.Length == 0) return false;
        ArgumentValue? root = null;
        foreach (var piece in parameter.Pieces)
        {
            if (!registers.TryGetValue(piece.Register, out var value) || input(value) is not { } part
                || part.Piece.Offset != piece.Offset || part.Piece.Width != piece.Width || !part.Root.Type.Equals(parameter.Type)
                || root is not null && !root.Equals(part.Root)) return false;
            root = part.Root;
        }
        return true;
    }
}
