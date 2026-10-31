using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class ScalarFramesRules
{
    [MachinePass("分支帧快照", 29, After = ["帧前类型", "标量栈实参"])]
    internal static void ForwardBranchFrameSnapshots(this RecoveryScope ctx)
    {
        var calls = new ManagedCallFrames(ctx.facts, ctx.owner.abi);
        // 聚合参数的分片读取仍用于划分类型生命期，不先拆走它们的初始化证据。
        var witnesses = new List<FrameWitness>();
        ctx.WitnessLoadedArguments(witnesses);
        ctx.WitnessLoadedReturns(witnesses);
        var preserved = witnesses.Where(w => ctx.types.Kind(w.Type) == TypeKind.Struct).Select(w => w.Call).ToHashSet();
        var lifetimes = FrameLifetimeSnapshots.Read(ctx.function, ctx.NoStackRead, calls.ArgumentSize, e => ctx.FrameOffset(e), preserved);
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (lifetimes.TryGetValue(block.Statements[i], out var mapped)) ctx.Rewriter.Replace(block, i, mapped);
        var replacements = FrameBranchSnapshots.Read(ctx.function, ctx.NoStackRead);
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (!replacements.TryGetValue(old, out var mapped))
                    continue;
                ctx.Rewriter.Replace(block, i, mapped);
            }

        if (replacements.Count > 0 || lifetimes.Count > 0)
            ctx.definitions = ctx.IndexDefinitions();
    }

    [MachinePass("帧快照", 32, After = ["帧区域"])]
    internal static void ForwardFrameSnapshots(this RecoveryScope ctx)
    {
        var pieces = FramePieceSnapshots.Read(ctx.function, ctx.NoStackRead, expression => ctx.FrameAccess(expression) is { } frame ? frame.Region.Offset + frame.Offset : ctx.FrameOffset(expression));
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (!pieces.TryGetValue(old, out var mapped))
                    continue;
                ctx.Rewriter.Replace(block, i, mapped);
            }

        var replacements = FrameSnapshots.Read(ctx.function, ctx.ruleTraces.Add, expression => ctx.FrameAccess(expression) is { } frame ? frame.Region.Offset + frame.Offset : ctx.FrameOffset(expression));
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (!replacements.TryGetValue(old, out var mapped))
                    continue;
                ctx.Rewriter.Replace(block, i, mapped);
            }

        if (pieces.Count > 0 || replacements.Count > 0)
            ctx.definitions = ctx.IndexDefinitions();
    }

    /// <summary>结构体地址已绑定到有界区域后，恢复地址不逃逸的整数计数槽和已定型的引用槽。</summary>
    [MachinePass("整数帧槽", 35, After = ["帧区域", "帧快照"])]
    internal static void PrepareScalarFrames(this RecoveryScope ctx)
    {
        ctx.InferTypes();
        var accesses = new List<(long Offset, int Width, Expr? Written)>();
        var escapes = new List<long>();
        void Visit(Expr expression)
        {
            if (expression is Load load && ctx.FrameOffset(load.Address) is { } offset)
                accesses.Add((offset, load.Width, null));
            else if (ctx.FrameOffset(expression) is { } escaped)
                escapes.Add(escaped);
            else
                foreach (var child in ExprMap.Children(expression))
                    Visit(child);
        }

        foreach (var statement in ctx.blocks.SelectMany(b => b.Statements))
        {
            if (ctx.State.Lowering.dropped.Contains(statement) || statement is Call call && (ctx.State.Frames.stackEnums.ContainsKey(call) || ctx.IsWriteBarrier(call)))
                continue;
            if (statement is Store store && ctx.FrameOffset(store.Target) is { } offset)
            {
                accesses.Add((offset, store.Value.Width, store.Value));
                Visit(store.Value);
            }
            else
                foreach (var operand in ExprMap.Operands(statement))
                    Visit(operand);
        }

        // 常量本身没有类型；至少一次整数计算或已定型整数写入提供证据。
        (bool Allowed, bool Integer) Written(Expr expression, HashSet<Variable> seen) => expression switch
        {
            Const => (true, false),
            Binary { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor } => (true, true),
            Ir.Convert { Kind: ConvKind.Truncate or ConvKind.ZeroExtend or ConvKind.SignExtend } convert => Written(convert.Operand, seen),
            Use use when ctx.State.Types.known.TryGetValue(use.Variable, out var type) && ctx.types.Kind(type) is TypeKind.Int or TypeKind.Bool => (true, true),
            Use use when seen.Add(use.Variable) && ctx.values.TryGetValue(use.Variable, out var value) => Written(value, seen),
            _ => (false, false),
        };
        var scalar = new Dictionary<long, FrameRegion>();
        foreach (var group in accesses.GroupBy(a => a.Offset))
        {
            var offset = group.Key;
            if (offset >= 0 || group.Select(a => a.Width).Distinct().ToArray() is not [var width and (32 or 64)] || escapes.Any(at => at <= offset) || ctx.State.Frames.frameRegions.Any(r => offset < r.Offset + r.Size && r.Offset < offset + width / 8) || accesses.Any(a => a.Offset != offset && offset < a.Offset + a.Width / 8 && a.Offset < offset + width / 8))
                continue;
            if (!group.Any(a => a.Written is null))
            {
                // 无读取的常量备份还须与每个调用的栈参数区域分离。
                if (group.All(a => a.Written is Const) && ctx.blocks.SelectMany(b => b.Statements).OfType<Call>().All(c => ctx.NoStackRead(c, offset, width)))
                    ctx.State.Lowering.dropped.UnionWith(ctx.blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => ctx.FrameOffset(s.Target) == offset));
                continue;
            }

            if (width == 64)
            {
                TypeRef? Reference(Expr value) => value is Use use && ctx.State.Types.known.TryGetValue(use.Variable, out var type) && ctx.types.Kind(type) == TypeKind.Reference ? type : null;
                var writes = group.Where(a => a.Written is not null).Select(a => a.Written!).ToArray();
                var candidates = writes.Select(Reference).OfType<TypeRef>().Distinct().ToArray();
                if (candidates.FirstOrDefault(t => candidates.All(other => ctx.types.IsAssignable(other, t))) is { } reference && writes.All(v => v is Const { Value: 0 } || Reference(v) is not null))
                    scalar[offset] = new(offset, reference, 8, ctx.StructLocal(reference, 64));
                continue;
            }

            var written = group.Where(a => a.Written is not null).Select(a => Written(a.Written!, [])).ToArray();
            if (!written.Any(w => w.Integer) || written.Any(w => !w.Allowed))
                continue;
            scalar[offset] = new(offset, ctx.types.Int32, 4, ctx.StructLocal(ctx.types.Int32, 32));
        }

        if (scalar.Count == 0)
            return;
        ctx.State.Frames.frameRegions.AddRange(scalar.Values);
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (ctx.State.Lowering.dropped.Contains(old) || old is Call call && ctx.State.Frames.stackEnums.ContainsKey(call))
                    continue;
                var mapped = ExprMap.MapOperands(old, e => ExprMap.Map(e, part => ctx.FrameOffset(part) is { } offset && scalar.TryGetValue(offset, out var region) ? new TypedFrame(region) : null));
                if (ReferenceEquals(old, mapped))
                    continue;
                ctx.Rewriter.Replace(block, i, mapped);
            }

        ctx.definitions = ctx.IndexDefinitions();
    }

    internal static bool NoStackRead(this RecoveryScope ctx, Call call, long offset, int width)
    {
        if (call.Op?.Kind is OpKind.InitClass or OpKind.RunClassConstructor or OpKind.InitMethodRgctx or OpKind.NewObject or OpKind.NewArray or OpKind.Box or OpKind.Unbox or OpKind.IsInst or OpKind.IsAssignableFrom or OpKind.TypeCheck or OpKind.ThrowIf or OpKind.NullCheck or OpKind.BoundsCheck or OpKind.Throw or OpKind.ThrowNew or OpKind.NewException or OpKind.Rethrow or OpKind.WriteBarrier or OpKind.MemoryBarrier or OpKind.CompareExchangeReference or OpKind.InterfaceInvokeData or OpKind.ResolveGenericVirtual or OpKind.BeginCatch or OpKind.EndCatch or OpKind.ResumeUnwind or OpKind.Terminate or OpKind.ThrowManaged)
            return true;
        return ctx.Resolve(call) is { } target && ctx.owner.abi.Classify(target, out _) is { } signature && (signature.MethodInfo is not null && signature.Arguments.All(a => a.Passing != Facts.Passing.Stack) || ctx.State.Frames.callStackAreas.TryGetValue(call.Address, out var area) && (offset + width / 8 <= area.Offset || offset >= area.Offset + area.Size));
    }
}
