using Cpp2CS.Ir;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

internal static class FrameArgumentSpan
{
    internal static (long Origin, Define[] Reads)? ReturnLoads(Expr value, IReadOnlyList<AbiPiece> abi, int size,
        IReadOnlyDictionary<Variable, Define> definitions, Func<Expr, long?> frameOffset)
    {
        var values = value is Intrinsic { Name: "diagnostic_return" } parts ? parts.Arguments : [value];
        if (values.Length != abi.Count) return null;
        var pieces = new List<(int Offset, int Width, long Frame)>();
        var reads = new List<Define>();
        for (var i = 0; i < values.Length; i++)
        {
            var piece = abi[i];
            if (Loaded(values[i], definitions) is not { } read || read.Load.Width != piece.Width
                || frameOffset(read.Load.Address) is not { } offset) return null;
            pieces.Add((piece.Offset, piece.Width, offset));
            reads.Add(read.Statement);
        }
        return Origin(size, pieces) is { } origin ? (origin, reads.ToArray()) : null;
    }

    internal static (Load Load, Define Statement)? Loaded(Expr expression, IReadOnlyDictionary<Variable, Define> definitions)
    {
        var seen = new HashSet<Variable>();
        while (expression is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var define)
            && use.Width == define.Value.Width)
        {
            var load = define.Value switch
            {
                Load direct => direct,
                Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: Load { Width: 8 or 16 or 32 } narrow } => narrow,
                _ => null,
            };
            if (load is not null) return (load, define);
            expression = define.Value;
        }
        return null;
    }

    internal static long? Origin(int size, IReadOnlyList<(int Offset, int Width, long Frame)> pieces)
    {
        if (size <= 0 || pieces.Count == 0) return null;
        var origin = pieces[0].Frame - pieces[0].Offset;
        if (origin >= 0 || origin + size > 0) return null;
        var covered = 0;
        foreach (var piece in pieces.OrderBy(p => p.Offset))
        {
            if (piece.Width is not (8 or 16 or 32 or 64 or 128) || piece.Offset != covered || piece.Frame - piece.Offset != origin) return null;
            covered += piece.Width / 8;
        }
        return covered == size ? origin : null;
    }
}
