using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class FrameArgumentsRules
{
    internal static void WitnessLoadedArguments(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        var loads = ctx.blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        (Load Load, Define Statement)? Loaded(Expr expression) => FrameArgumentSpan.Loaded(expression, loads);
        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            var registers = CallResolution.ArgumentsOf(call);
            if (!registers.Values.Any(e => Loaded(e) is { } read && ctx.FrameOffset(read.Load.Address) is not null) || ctx.Resolve(call) is not { } callee || ctx.owner.abi.Classify(callee, out _) is not { } signature)
                continue;
            foreach (var argument in signature.Arguments.Where(ctx.RegisterStruct))
            {
                var pieces = new List<(int Offset, int Width, long Frame)>();
                var reads = new List<Define>();
                foreach (var piece in argument.Pieces)
                {
                    if (!registers.TryGetValue(piece.Register, out var expression) || Loaded(expression) is not { } read || read.Load.Width != piece.Width || ctx.FrameOffset(read.Load.Address) is not { } offset)
                        break;
                    pieces.Add((piece.Offset, piece.Width, offset));
                    reads.Add(read.Statement);
                }

                if (pieces.Count != argument.Pieces.Length || FrameArgumentSpan.Origin(ctx.types.Size(argument.Type), pieces) is not { } origin)
                    continue;
                ctx.State.Calls.callBindings.Commit(call, callee);
                foreach (var read in reads)
                    witnesses.Add(new(origin, argument.Type, read, false));
            }
        }
    }

    internal static void WitnessLoadedReturns(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        if (ctx.owner.abi.Classify(ctx.method, out _)?.Return is not { } returned || !ctx.RegisterStruct(returned))
            return;
        var definitions = ctx.blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        foreach (var statement in ctx.blocks.SelectMany(b => b.Statements).OfType<Return>())
        {
            if (statement.Value is not { } value || FrameArgumentSpan.ReturnLoads(value, returned.Pieces, ctx.types.Size(returned.Type), definitions, e => ctx.FrameOffset(e)) is not { } span)
                continue;
            foreach (var read in span.Reads)
                witnesses.Add(new(span.Origin, returned.Type, read, false));
        }
    }
}
