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
                if (ctx.TypedFrameRead(witnesses, origin, argument.Type, reads)) continue;
                ctx.WitnessReadInitialization(witnesses, origin, argument.Type, reads);
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
            if (ctx.RegisterStruct(returned) && ctx.TypedFrameRead(witnesses, span.Origin, returned.Type, span.Reads)) continue;
            if (ctx.RegisterStruct(returned)) ctx.WitnessReadInitialization(witnesses, span.Origin, returned.Type, span.Reads);
            foreach (var read in span.Reads)
                witnesses.Add(new(span.Origin, returned.Type, read, false));
        }
    }

    /// <summary>寄存器传参可按字段重新组装结构体；同块已有写入给出兼容叶子时，不再用目标结构体覆盖源区域。</summary>
    internal static bool TypedFrameRead(this RecoveryScope ctx, List<FrameWitness> witnesses, long offset, TypeRef type, IEnumerable<Define> reads)
    {
        var leaves = ctx.ScalarStructPaths(type).ToArray();
        if (leaves.Length == 0) return false;
        return witnesses.Any(w => w.Writes && ctx.types.Kind(w.Type) == TypeKind.Struct
            && w.Offset <= offset && offset + ctx.types.Size(type) <= w.Offset + ctx.types.Size(w.Type)
            && reads.All(read => ctx.SameBlockBefore(w.Call, read))
            && leaves.All(leaf => ctx.ScalarStructPaths(w.Type).Any(source => w.Offset + source.Offset == offset + leaf.Offset && source.Type.Equals(leaf.Type))));
    }

    internal static void WitnessReadInitialization(this RecoveryScope ctx, List<FrameWitness> witnesses, long offset, TypeRef type, IEnumerable<Define> reads)
    {
        var sites = ctx.blocks.SelectMany(b => b.Statements.Select((s, i) => (Block: b, Statement: s, Index: i)))
            .Where(s => reads.Contains(s.Statement)).ToArray();
        if (sites.Length == 0 || sites.Select(s => s.Block).Distinct().Count() != 1) return;
        var block = sites[0].Block;
        var prefix = block.Statements.Take(sites.Min(s => s.Index)).ToList();
        var seen = new HashSet<Cpp2CS.Machine.Flow.Block> { block };
        while (prefix.Count < 128 && block.Predecessors.ToArray() is [var parent]
            && parent.NormalSuccessors.ToArray() is [var next] && next == block && seen.Add(parent))
        {
            prefix.InsertRange(0, parent.Statements);
            block = parent;
        }

        // 判空和写屏障不读取这些局部字段；其他调用和地址读取仍由覆盖检查截断。
        prefix.RemoveAll(s => s is Jump or Nop || s is Call { Op.Kind: OpKind.NullCheck or OpKind.WriteBarrier });
        if (FrameCopySpans.FullWriteBefore(prefix, prefix.Count, offset, ctx.types.Size(type),
            ctx.ScalarStructPaths(type).Select(p => (p.Offset, ctx.types.Size(p.Type))).ToArray(), e => ctx.FrameOffset(e)) is { } start)
            witnesses.Add(new(offset, type, start, true));
    }
}
