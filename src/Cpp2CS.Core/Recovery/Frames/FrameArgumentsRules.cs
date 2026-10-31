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
                        continue;
                    pieces.Add((piece.Offset, piece.Width, offset));
                    reads.Add(read.Statement);
                }

                if (pieces.Count == 0)
                    continue;
                var origin = pieces[0].Frame - pieces[0].Offset;
                var size = ctx.types.Size(argument.Type);
                // 调用签名也能给部分栈片定型；其他分量可来自寄存器，不推断它们已写入栈。
                if (origin >= 0 || origin + size > 0 || pieces.Any(p => p.Frame - p.Offset != origin || p.Offset < 0 || p.Offset + p.Width / 8 > size))
                    continue;
                ctx.State.Calls.callBindings.Commit(call, callee);
                foreach (var read in reads)
                    witnesses.Add(new(origin, argument.Type, read, false));
            }
        }
    }

    internal static void WitnessLoadedReturns(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        if (ctx.owner.abi.Classify(ctx.method, out _)?.Return is not { } returned
            || !ctx.RegisterStruct(returned) && !(returned.Passing == Facts.Passing.Registers && returned.Pieces.Length == 1
                && ctx.types.Kind(returned.Type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference))
            return;
        var definitions = ctx.blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target);
        foreach (var statement in ctx.blocks.SelectMany(b => b.Statements).OfType<Return>())
        {
            if (statement.Value is not { } value || FrameArgumentSpan.ReturnLoads(value, returned.Pieces, ctx.types.Size(returned.Type), definitions, e => ctx.FrameOffset(e)) is not { } span)
                continue;
            // 返回接口只是读取约束；已有兼容的引用写入类型不需要另建冲突区域。
            var existing = witnesses.Where(w => w.Offset == span.Origin).ToArray();
            if (ctx.types.Kind(returned.Type) == TypeKind.Reference && existing.Length != 0
                && existing.All(w => ctx.types.Kind(w.Type) == TypeKind.Reference && ctx.types.IsAssignable(w.Type, returned.Type))) continue;
            foreach (var read in span.Reads)
                witnesses.Add(new(span.Origin, returned.Type, read, false));
        }
    }
}
