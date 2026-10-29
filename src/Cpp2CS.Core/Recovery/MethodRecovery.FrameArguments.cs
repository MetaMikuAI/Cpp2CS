using Cpp2CS.Ir;
using Cpp2CS.Facts;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>值类型实参的全部寄存器片读取同一段栈时，以精确调用签名确定整个区域。</summary>
        private void WitnessLoadedArguments(List<FrameWitness> witnesses)
        {
            var loads = blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
            (Load Load, Define Statement)? Loaded(Expr expression) => FrameArgumentSpan.Loaded(expression, loads);
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                var registers = ArgumentsOf(call);
                if (!registers.Values.Any(e => Loaded(e) is { } read && FrameOffset(read.Load.Address) is not null)
                    || Resolve(call) is not { } callee || owner.abi.Classify(callee, out _) is not { } signature) continue;
                foreach (var argument in signature.Arguments.Where(RegisterStruct))
                {
                    var pieces = new List<(int Offset, int Width, long Frame)>();
                    var reads = new List<Define>();
                    foreach (var piece in argument.Pieces)
                    {
                        if (!registers.TryGetValue(piece.Register, out var expression) || Loaded(expression) is not { } read
                            || read.Load.Width != piece.Width || FrameOffset(read.Load.Address) is not { } offset) break;
                        pieces.Add((piece.Offset, piece.Width, offset));
                        reads.Add(read.Statement);
                    }
                    if (pieces.Count != argument.Pieces.Length || FrameArgumentSpan.Origin(types.Size(argument.Type), pieces) is not { } origin) continue;
                    callBindings.Commit(call, callee);
                    foreach (var read in reads) witnesses.Add(new(origin, argument.Type, read, false));
                }
            }
        }

        /// <summary>返回值的全部 ABI 片来自同一段栈时，返回签名提供精确区域类型。</summary>
        private void WitnessLoadedReturns(List<FrameWitness> witnesses)
        {
            if (owner.abi.Classify(method, out _)?.Return is not { } returned || !RegisterStruct(returned)) return;
            var definitions = blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
            foreach (var statement in blocks.SelectMany(b => b.Statements).OfType<Return>())
            {
                if (statement.Value is not { } value || FrameArgumentSpan.ReturnLoads(value, returned.Pieces,
                    types.Size(returned.Type), definitions, e => FrameOffset(e)) is not { } span) continue;
                foreach (var read in span.Reads) witnesses.Add(new(span.Origin, returned.Type, read, false));
            }
        }
    }
}

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
