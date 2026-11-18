using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Locations;

/// <summary>各段按目标内的字节位置组成一个值，必须恰好覆盖整个存储区。</summary>
internal static class WholeWriteSource
{
    public static BoundSource? FromPieces(IEnumerable<BoundPiece> pieces, int bytes)
    {
        var ordered = pieces.OrderBy(p => p.ValueOffset).ToArray();
        int cursor = 0;
        foreach (var piece in ordered)
        {
            if (piece.ValueOffset != cursor || piece.Length <= 0 || piece.Length > bytes - cursor) return null;
            cursor += piece.Length;
        }
        if (cursor != bytes || ordered.Length == 0) return null;
        return ordered.Length == 1 ? ordered[0].Source : new PiecesSource([.. ordered]);
    }
}
