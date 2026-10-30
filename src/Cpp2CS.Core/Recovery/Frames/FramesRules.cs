using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class FramesRules
{
    internal static bool ContainsFrameType(this RecoveryScope ctx, FrameRegion outer, long offset, TypeRef type) => outer.Offset == offset && outer.Type.Equals(type) || ctx.StructPaths(outer.Type).Any(p => outer.Offset + p.Offset == offset && p.Type.Equals(type));
    /// <summary>先解析接收者及虚调用返回类型，避免帧区域只看见直调签名而提前固定错误的栈槽类型。</summary>
    [MachinePass("帧前类型", 29, After = ["异常值", "栈上调用"])]
    internal static void PrepareFrameTypes(this RecoveryScope ctx)
    {
        ctx.InferTypes();
        ctx.NormalizeCheckedObjects();
        for (var round = 0; round < 8 && JoinedFieldReads.Run(ctx.function, phi => phi.Sources.All(v => ctx.State.Types.known.TryGetValue(v, out var type) && ctx.types.Kind(type) == TypeKind.Reference) && phi.Sources.Select(v => ctx.State.Types.known[v]).Distinct().Count() > 1 || phi.Sources.All(ctx.FieldAddress)); round++)
        {
            Cpp2CS.Machine.Ssa.Propagate.Run(ctx.function, ctx.Dominators);
            ctx.blocks = ctx.function.Blocks;
            ctx.definitions = ctx.IndexDefinitions();
            ctx.InferTypes();
        }

        ctx.NormalizePinnedArrays(true);
        ctx.PrepareArrayCursors();
    }

    internal static bool FieldAddress(this RecoveryScope ctx, Variable variable)
    {
        Expr root = new Use(variable, 64);
        long offset = 0;
        var seen = new HashSet<Variable>();
        for (var depth = 0; depth < 16; depth++)
        {
            if (root is Binary { Op: BinOp.Add, Right: Const displacement } addition)
            {
                offset += displacement.Signed;
                root = addition.Left;
                continue;
            }

            if (root is not Use use || !seen.Add(use.Variable))
                break;
            if (ctx.values.GetValueOrDefault(use.Variable) is Use or Symbol or Binary { Op: BinOp.Add, Right: Const })
            {
                root = ctx.values[use.Variable];
                continue;
            }

            if (ctx.phis.GetValueOrDefault(use.Variable) is { Sources: [var source] })
            {
                root = new Use(source, 64);
                continue;
            }

            break;
        }

        return root is Symbol { Kind: SymbolKind.StaticFields or SymbolKind.ThreadStaticFields } || offset > 0 && ctx.TypeOfAddressBase(root) is { } type && ManagedTypes.IsReferenceType(type);
    }

    [MachinePass("帧后数组地址", 37, After = ["整数帧槽"])]
    internal static void PrepareFrameArrayAddresses(this RecoveryScope ctx)
    {
        ctx.InferTypes();
        ctx.NormalizePinnedArrays(false);
        ctx.PrepareArrayCursors();
    }

    internal static void NormalizePinnedArrays(this RecoveryScope ctx, bool simplifyFlow)
    {
        if (PinnedArrayRecognition.Run(ctx.function, e => ctx.TypeOfAddressBase(e) is ArrayRef { IsVector: true } array && ctx.types.Kind(array.Element) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double ? array : null) > 0)
        {
            ctx.RemoveDeadDefinitions();
            // 异常片段已绑定基本块；此处只删纯定义，不改变受保护控制流。
            if (simplifyFlow && ctx.State.Exceptions.exceptionLayout is not { Succeeded: true })
                while (Cpp2CS.Machine.Ssa.ControlFlow.Simplify(ctx.function))
                    ctx.function.Problems.AddRange(Cpp2CS.Machine.Ssa.Lowering.Cleanup(ctx.function));
            ctx.blocks = ctx.function.Blocks;
            ctx.definitions = ctx.IndexDefinitions();
            ctx.InferTypes();
        }
    }

    /// <summary>只有精确调用签名提供类型；普通访存宽度不能定型。异型重叠先拒绝，嵌套字段见证合并到外根。</summary>
    [MachinePass("帧区域", 30, After = ["异常值", "栈上调用", "帧前类型", "分支帧快照"])]
    internal static RecoveryFailure? PrepareFrames(this RecoveryScope ctx)
    {
        var witnesses = new List<FrameWitness>();
        void Bind(Expr expression, TypeRef type, Call call, bool writes = false)
        {
            // 结构体，以及按地址传递的基元/引用（基元值类型实例方法的 this，如 x.ToString()；out/ref 参数）：后者是一个该类型的局部变量。
            if (ctx.types.Kind(type) is TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference && ctx.FrameOffset(expression) is { } offset && ctx.types.Size(type) > 0)
                witnesses.Add(new(offset, type, call, writes));
        }

        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (ctx.State.Frames.stackEnums.ContainsKey(call))
                continue;
            if (!call.Arguments.Any(argument => ctx.FrameOffset(argument) is not null))
                continue;
            if (call.Op is { Kind: OpKind.InvokeGeneric, Operand: MethodRef invoked })
            {
                for (var i = 0; i < invoked.Method.Parameters.Count; i++)
                {
                    var type = CallResolution.Concrete(invoked, invoked.Method.Parameters[i].Type);
                    if (!ManagedTypes.IsReferenceType(type))
                        Bind(call.Arguments[i + 1], type is ByRefRef reference ? reference.Element : type, call);
                }

                var returned = CallResolution.Concrete(invoked, invoked.Method.ReturnType);
                if (!ManagedTypes.IsVoid(returned))
                    Bind(call.Arguments[^1], returned, call, true);
                continue;
            }

            // 装箱提供精确值类型；标量的到达写入划出生命期，允许后续结构体复用同一物理槽。
            if (call.Op is { Kind: OpKind.Box, Operand: TypeRef boxedType } && call.Arguments.LastOrDefault() is { } data && ctx.types.Kind(boxedType) is TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)
            {
                Bind(data, boxedType, call);
                if (ctx.types.Kind(boxedType) != TypeKind.Struct && ctx.FrameOffset(data) is { } offset)
                {
                    var block = ctx.blocks.Single(b => b.Statements.Contains(call));
                    if (ctx.ReachingStackStore(block, block.Statements.IndexOf(call), offset, [], ctx.types.Size(boxedType) * 8) is { } store)
                        witnesses.Add(new(offset, boxedType, store, true));
                }
            }

            if (ctx.Resolve(call) is not { } callee || ctx.owner.abi.Classify(callee, out _) is not { } signature)
                continue;
            // 帧区域按这次解析的签名定型；之后类型变化也不能换成另一个 ICF 候选，否则区域类型与调用不一致。
            ctx.State.Calls.callBindings.Commit(call, callee);
            var registers = CallResolution.ArgumentsOf(call);
            foreach (var argument in signature.Arguments.Concat(signature.Return is { Passing: Passing.Indirect } ret ? [ret] : []))
            {
                if (argument.Pieces.Length != 1 || !registers.TryGetValue(argument.Pieces[0].Register, out var expression))
                    continue;
                if (argument.Type is ByRefRef reference)
                    Bind(expression, reference.Element, call);
                else if (argument.Passing == Passing.Indirect)
                    Bind(expression, argument.Type, call, ReferenceEquals(argument, signature.Return));
            }
        }

        ctx.WitnessStoredArguments(witnesses);
        ctx.WitnessLoadedArguments(witnesses);
        ctx.WitnessLoadedReturns(witnesses);
        if (ctx.WitnessStoredResults(witnesses) is { } resultFailure)
            return resultFailure;
        if (ctx.WitnessFieldCopies(witnesses) is { } fieldFailure)
            return fieldFailure;
        ctx.WitnessFrameCopies(witnesses);
        if (ctx.DiscoverArrayFrameCopies(witnesses) is { } arrayFailure)
            return arrayFailure;
        var regions = witnesses.DistinctBy(w => (w.Offset, w.Type)).Select(w => new FrameRegion(w.Offset, w.Type, ctx.types.Size(w.Type), ctx.StructLocal(w.Type, ctx.ScalarWidth(w.Type)))).OrderByDescending(r => r.Size).ThenBy(r => r.Offset).ToArray();
        foreach (var region in regions)
        {
            if (regions.Any(other => other != region && region.Offset < other.Offset + other.Size && other.Offset < region.Offset + region.Size && !ctx.ContainsFrameType(region, other.Offset, other.Type) && !ctx.ContainsFrameType(other, region.Offset, region.Type)))
            {
                ctx.State.Frames.conflictingFrames.Add(region.Offset);
                continue;
            }

            if (!ctx.State.Frames.frameRegions.Any(outer => ctx.ContainsFrameType(outer, region.Offset, region.Type)))
            {
                // 单字段包装可能与内部字段同尺寸；外根后被发现时仍合并已登记的内层区域。
                ctx.State.Frames.frameRegions.RemoveAll(inner => ctx.ContainsFrameType(region, inner.Offset, inner.Type));
                ctx.State.Frames.frameRegions.Add(region);
            }
        }

        ctx.PrepareColoredFrames(regions, witnesses);
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (ctx.State.Frames.stackEnumStorage.Contains(old))
                    continue;
                var mapped = ExprMap.MapOperands(old, e => ExprMap.Map(e, part =>
                {
                    if (ctx.FrameOffset(part) is not { } offset)
                        return null;
                    // 同一处落在多个区域（生命期拆分不完整）：不绑定，留给栈槽类型冲突报洞。
                    var matching = ctx.State.Frames.frameRegions.Where(r => offset >= r.Offset && offset < r.Offset + r.Size && (!ctx.State.Frames.frameLives.TryGetValue(r, out var live) || live.Contains(old))).Take(2).ToArray();
                    if (matching is not [var region])
                    {
                        if (matching.Length > 1)
                            ctx.State.Frames.conflictingFrames.Add(offset);
                        return null;
                    }

                    Expr root = new TypedFrame(region);
                    return offset == region.Offset ? root : new Binary(BinOp.Add, root, new Const((ulong)(offset - region.Offset), 64), 64);
                }));
                if (ReferenceEquals(old, mapped))
                    continue;
                // 若隐藏槽同时属于托管区域，其写入也有字段语义，不能仅作为调用元数据删去。
                ctx.State.Lowering.dropped.Remove(old);
                ctx.Rewriter.Replace(block, i, mapped);
            }

        // IR 改写后，定义索引按新语句重建。
        ctx.definitions = ctx.IndexDefinitions();
        ctx.PrepareFrameInitializers();
        return null;
    }

    internal static RecoveryFailure? DiscoverArrayFrameCopies(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        if (!witnesses.Any(w => w.Type is ArrayRef || ctx.StructPaths(w.Type).Any(p => p.Type is ArrayRef)))
            return null;
        for (var round = 0; round < 8; round++)
        {
            var candidates = witnesses.DistinctBy(w => (w.Offset, w.Type)).Select(w => new FrameRegion(w.Offset, w.Type, ctx.types.Size(w.Type), ctx.StructLocal(w.Type, ctx.ScalarWidth(w.Type)))).OrderByDescending(r => r.Size).ToArray();
            // 发现阶段只使用不冲突的精确布局；复用栈槽仍由最终生命期分析处理。
            ctx.State.Frames.discoveryFrames = candidates.Where(r => !candidates.Any(other => other != r && r.Offset < other.Offset + other.Size && other.Offset < r.Offset + r.Size && !ctx.ContainsFrameType(r, other.Offset, other.Type) && !ctx.ContainsFrameType(other, r.Offset, r.Type))).Where(r => !candidates.Any(outer => outer != r && ctx.ContainsFrameType(outer, r.Offset, r.Type))).ToArray();
            ctx.State.Structs.fragmentLocals.Clear();
            ctx.InferTypes();
            ctx.PrepareArrayCursors();
            var count = witnesses.Count;
            if (ctx.WitnessFieldCopies(witnesses) is { } fieldFailure)
                return fieldFailure;
            ctx.WitnessFrameCopies(witnesses);
            if (witnesses.Count == count)
                break;
        }

        ctx.State.Frames.discoveryFrames = [];
        ctx.State.Structs.fragmentLocals.Clear();
        return null;
    }

    internal static void WitnessStoredArguments(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        var stores = ctx.blocks.SelectMany(b => b.Statements).OfType<Store>().Where(s => s.Value is Use { Variable.Version: 0 } && ctx.FrameOffset(s.Target) is not null).ToLookup(s => ((Use)s.Value).Variable.Storage);
        foreach (var group in ctx.State.Signature.structArguments.GroupBy(p => p.Value.Root))
        {
            long? origin = null;
            Store? first = null;
            foreach (var (register, argument) in group)
            {
                var matches = stores[register].Where(s => s.Value.Width == argument.Piece.Width).ToArray();
                if (matches is not [var store])
                {
                    origin = null;
                    break;
                }

                var at = ctx.FrameOffset(store.Target)!.Value - argument.Piece.Offset;
                if (origin is not null && origin != at)
                {
                    origin = null;
                    break;
                }

                origin = at;
                first ??= store;
            }

            if (origin is not { } offset || first is null || offset >= 0 || offset + ctx.types.Size(group.Key.Type) > 0)
                continue;
            witnesses.Add(new(offset, group.Key.Type, first, true));
        }
    }

    internal static RecoveryFailure? WitnessStoredResults(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        var stores = ctx.blocks.SelectMany(b => b.Statements).OfType<Store>().Select(s => (Store: s, Offset: s.Value is Use ? ctx.FrameOffset(s.Target) : null)).Where(p => p.Offset is not null).ToLookup(p => ((Use)p.Store.Value).Variable);
        if (stores.Count == 0)
            return null;
        foreach (var call in ctx.blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (!call.Defines.Any(d => d is not null && stores.Contains(d)))
                continue;
            if (ctx.Resolve(call) is not { } callee || ctx.owner.abi.Classify(callee, out _)?.Return is not { } returned || !ctx.RegisterStruct(returned))
                continue;
            long? origin = null;
            foreach (var piece in returned.Pieces)
            {
                var index = Array.IndexOf(call.Results, piece.Register);
                var written = index >= 0 && index < call.Defines.Length && call.Defines[index] is { } defined ? stores[defined].Where(p => p.Store.Value.Width == piece.Width).Select(p => p.Offset!.Value - piece.Offset).ToArray() : [];
                if (written is not [var at] || origin is not null && origin != at)
                {
                    origin = null;
                    break;
                }

                origin = at;
            }

            if (origin is not { } offset)
                continue;
            ctx.State.Calls.callBindings.Commit(call, callee);
            witnesses.Add(new(offset, returned.Type, call, false));
        }

        // 结构体值的整体读取（静态字段、对象或 ByRef 根上的结构体字段）原样写入栈槽：例如 await UniTask.CompletedTask 把静态字段拷进临时 awaiter。
        foreach (var group in stores)
        {
            if (!ctx.values.TryGetValue(group.Key, out var value) || value is not Load { Width: 64 or 128 } load)
                continue;
            if (!ctx.CopyRanges(load.Address, load.Width).TryGet(out var candidates, out var failure))
                return failure;
            var ranges = candidates.Where(r => r.Offset == 0 && ctx.types.Size(r.Type) * 8 == load.Width).ToArray();
            var outer = ranges.Where(r => ranges.All(q => q == r || ctx.StructPaths(r.Type).Any(p => p.Offset == 0 && p.Type.Equals(q.Type)))).Select(r => r.Type).Distinct().ToArray();
            if (outer is not [var type])
                continue;
            foreach (var (store, offset) in group)
                if (store.Value.Width == load.Width)
                    witnesses.Add(new(offset!.Value, type, store, false));
        }

        return null;
    }

    internal static RecoveryFailure? WitnessFieldCopies(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        foreach (var block in ctx.blocks)
        {
            var copies = new List<(long Offset, CopyRange Range, Store Store, int Width, bool Writes)>();
            foreach (var store in block.Statements.OfType<Store>())
            {
                if (store.Value is not Use use || !ctx.values.TryGetValue(use.Variable, out var value) || FrameCopiesRules.CopiedLoad(value) is not { Width: 32 or 64 or 128 } load || load.Width != use.Width)
                    continue;
                if (ctx.FrameOffset(store.Target) is { } to && ctx.FrameOffset(load.Address) is null)
                {
                    if (!ctx.CopyRanges(load.Address, load.Width).TryGet(out var ranges, out var failure))
                        return failure;
                    copies.AddRange(ranges.Select(r => (to - r.Offset, r, store, load.Width, true)));
                }

                if (ctx.FrameOffset(load.Address) is { } from && ctx.FrameOffset(store.Target) is null)
                {
                    if (!ctx.CopyRanges(store.Target, load.Width).TryGet(out var ranges, out var failure))
                        return failure;
                    copies.AddRange(ranges.Select(r => (from - r.Offset, r, store, load.Width, false)));
                }
            }

            foreach (var group in copies.GroupBy(c => (c.Offset, c.Range.Type, c.Range.Root, c.Writes)))
            {
                var (offset, type, _, writes) = group.Key;
                var size = ctx.types.Size(type);
                if (offset >= 0 || offset + size > 0)
                    continue;
                var first = group.First().Store;
                // 已有读取签名不能代替本次完整写入；连续复制的起点切断旧栈值的生命期。
                var definition = writes && FrameCopySpans.WriteStart(block.Statements, group.Select(c => c.Store)) is { } start ? start : null;
                if (witnesses.Any(w => w.Offset == offset && w.Type.Equals(type) && (definition is null || ReferenceEquals(w.Call, definition))))
                    continue;
                var covered = group.SelectMany(c => Enumerable.Range(c.Range.Offset, c.Width / 8)).ToHashSet();
                var leaves = ctx.StructPaths(type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
                if (type is GenericParameterRef { NativeAggregate: not null } ? Enumerable.Range(0, size).Any(b => !covered.Contains(b)) : leaves.Length == 0 || leaves.Any(p => Enumerable.Range(p.Offset, ctx.types.Size(p.Type)).Any(b => !covered.Contains(b))))
                    continue;
                witnesses.Add(new(offset, type, definition ?? first, definition is not null));
            }
        }

        return null;
    }

    internal static void WitnessFrameCopies(this RecoveryScope ctx, List<FrameWitness> witnesses)
    {
        var sites = ctx.blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).Where(p => p.Statement is Define).ToDictionary(p => ((Define)p.Statement).Target);
        TypeRef? ReachingType(Variable value, long offset)
        {
            if (!sites.TryGetValue(value, out var site))
                return null;
            var block = site.Block;
            var position = site.Index;
            var seen = new HashSet<Block>();
            while (seen.Add(block))
            {
                foreach (var statement in block.Statements.Take(position).Reverse())
                {
                    var writers = witnesses.Where(w => w.Offset == offset && ReferenceEquals(w.Call, statement) && (w.Writes || w.Call is Store)).Select(w => w.Type).Distinct().ToArray();
                    if (writers.Length > 0)
                        return writers is [var type] ? type : null;
                    if (statement is Call call && !ctx.IsWriteBarrier(call) && call.Arguments.Any(a => ctx.FrameOffset(a) == offset))
                        return null;
                }

                if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block)
                    return null;
                block = parent;
                position = block.Statements.Count;
            }

            return null;
        }

        var copies = new List<(long From, long To, int Width, Stmt Store, Variable Value)>();
        foreach (var store in ctx.blocks.SelectMany(b => b.Statements).OfType<Store>())
            if (store.Value is Use { Variable: var v } use && ctx.values.TryGetValue(v, out var value) && FrameCopiesRules.CopiedLoad(value) is { Width: 64 or 128 or 32 } load && load.Width == use.Width && ctx.FrameOffset(load.Address) is { } from && ctx.FrameOffset(store.Target) is { } to)
                copies.Add((from, to, load.Width, store, v));
        if (copies.Count == 0)
            return;
        for (var round = 0; round < 8; round++)
        {
            var added = false;
            foreach (var known in witnesses.DistinctBy(w => (w.Offset, w.Type)).ToArray())
            {
                var size = ctx.types.Size(known.Type);
                var leaves = ctx.StructPaths(known.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
                var ambiguous = witnesses.Any(w => w.Offset == known.Offset && !w.Type.Equals(known.Type) && !ctx.StructPaths(known.Type).Any(p => p.Offset == 0 && p.Type.Equals(w.Type)) && !ctx.StructPaths(w.Type).Any(p => p.Offset == 0 && p.Type.Equals(known.Type)));
                foreach (var forward in new[]
                {
                    true,
                    false
                }

                )
                    foreach (var group in copies.Where(c => (forward ? c.From : c.To) >= known.Offset && (forward ? c.From : c.To) < known.Offset + size)// 复用的源槽按本次读取前的完整写入定型，不能沿另一生命期的类型传播。
                    .Where(c => !forward || !ambiguous || known.Type.Equals(ReachingType(c.Value, known.Offset))).GroupBy(c => forward ? c.To - c.From : c.From - c.To))
                    {
                        var other = known.Offset + group.Key;
                        // 调用上的同类型读取见证不能替代复制写入点；复用槽需要该定义切断旧生命期。
                        if (witnesses.Any(w => w.Offset == other && w.Type.Equals(known.Type) && (!forward || ReferenceEquals(w.Call, group.First().Store))))
                            continue;
                        // 明确来源的正向复制也可能覆盖一个已被复用的槽；保留新类型见证，交给生命期分析拆分。
                        // 反向传播不能覆盖调用签名；正向只使用本次读取已经确定的类型。
                        if (witnesses.Any(w => w.Offset == other) && !forward)
                            continue;
                        var covered = new HashSet<long>();
                        foreach (var c in group)
                            for (var k = 0; k < c.Width / 8; k++)
                                covered.Add((forward ? c.From : c.To) - known.Offset + k);
                        if (group.Any(c => (forward ? c.From : c.To) + c.Width / 8 > known.Offset + size) || (known.Type is GenericParameterRef { NativeAggregate: not null } ? Enumerable.Range(0, size).Any(b => !covered.Contains(b)) : leaves.Any(p => Enumerable.Range(p.Offset, ctx.types.Size(p.Type)).Any(b => !covered.Contains(b)))))
                            continue;
                        witnesses.Add(new(other, known.Type, group.First().Store, false));
                        added = true;
                    }
            }

            if (!added)
                break;
        }
    }

    internal static int ScalarWidth(this RecoveryScope ctx, TypeRef type) => ctx.types.Kind(type) switch
    {
        TypeKind.Struct => 0,
        TypeKind.Bool => 8,
        TypeKind.Reference => 64,
        _ => ctx.types.Bits(type),
    };
    internal static bool FrameZero(this RecoveryScope ctx, Expr expression, HashSet<Variable>? active = null)
    {
        active ??= [];
        return expression switch
        {
            Const { Value: 0 } => true,
            Ir.Convert c => ctx.FrameZero(c.Operand, active),
            Insert i => ctx.FrameZero(i.Base, active) && ctx.FrameZero(i.Value, active),
            Use u when active.Add(u.Variable) && ctx.values.TryGetValue(u.Variable, out var value) => ctx.FrameZero(value, active),
            _ => false,
        };
    }

    internal static void PrepareFrameInitializers(this RecoveryScope ctx)
    {
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Store first || ctx.FrameAccess(first.Target) is not { } start || !ctx.FrameZero(first.Value))
                    continue;
                var region = start.Region;
                var stores = new List<Store>();
                var covered = new HashSet<long>();
                for (var j = i; j < block.Statements.Count; j++)
                {
                    if (block.Statements[j] is not Store store || ctx.FrameAccess(store.Target) is not { } access || access.Region != region || !ctx.FrameZero(store.Value) || access.Offset < 0 || access.Offset + store.Value.Width / 8 > region.Size)
                        break;
                    stores.Add(store);
                    for (var k = 0; k < store.Value.Width / 8; k++)
                        covered.Add(access.Offset + k);
                }

                if (covered.Count != region.Size)
                    continue;
                ctx.State.Frames.frameInitializers[first] = ctx.types.Kind(region.Type) == TypeKind.Struct ? [new ManagedStore(first.Address, new IndirectValue(new AddressValue(region.Local), region.Type), new ComposedValue(region.Type, []))] : [new ManagedAssignment(first.Address, region.Local, new ConstantValue(0, region.Type, region.Local.Width))];
                foreach (var store in stores.Skip(1))
                    ctx.State.Lowering.dropped.Add(store);
                i += stores.Count - 1;
            }
    }

    /// <summary>帧区域的初始化语句（清零、拷贝入）替代原语句。</summary>
    [StatementRule(20)]
    internal static bool LowerFrameInitializer(this LoweringScope ctx, Block block, Stmt statement, List<ManagedStatement> output)
    {
        if (!ctx.State.Frames.frameInitializers.TryGetValue(statement, out var initialization))
            return false;
        output.AddRange(initialization);
        return true;
    }

    [StoreRule(10)]
    internal static RecoveryResult<bool> StoreFrameZero(this LoweringScope ctx, Store store, List<ManagedStatement> output)
    {
        if (ctx.Values.FrameAccess(store.Target) is not { } frame || !ctx.Values.FrameZero(store.Value))
            return false;
        // 一次清零覆盖相邻的多个帧区域（如两个 out float）：按区域逐个清零，每个区域须被完整覆盖。
        if (frame.Offset + store.Value.Width / 8 > frame.Region.Size)
        {
            var start = frame.Region.Offset + frame.Offset;
            var end = start + store.Value.Width / 8;
            var covered = ctx.State.Frames.frameRegions.Where(r => r.Offset < end && start < r.Offset + r.Size).OrderBy(r => r.Offset).ToArray();
            if (covered.Any(r => r.Offset < start || r.Offset + r.Size > end) || covered.Sum(r => (long)r.Size) != end - start)
                return false;
            foreach (var region in covered)
            {
                if (!ctx.Values.FrameLocation(region, 0, region.Size * 8).TryGet(out var whole, out var failure))
                    return failure;
                foreach (var leaf in whole is Fragment parts ? parts.Parts.Select(p => p.Value) : [whole])
                    output.Add(FramesRules.StoreTo(store.Address, leaf, new ConstantValue(0, leaf.Type, leaf.Width)));
            }

            return true;
        }

        // 不先把 q 零值强行缩成 ulong；按区域布局逐个验证完整覆盖的叶子。
        if (!ctx.Values.FrameLocation(frame.Region, frame.Offset, store.Value.Width).TryGet(out var location, out var locationFailure))
            return locationFailure;
        foreach (var leaf in location is Fragment fragment ? fragment.Parts.Select(p => p.Value) : [location])
            output.Add(FramesRules.StoreTo(store.Address, leaf, new ConstantValue(0, leaf.Type, leaf.Width)));
        return true;
    }

    /// <summary>写入存储位置；标量帧区域本身是局部变量，写入即赋值。</summary>
    internal static ManagedStatement StoreTo(ulong address, ManagedValue target, ManagedValue value) => target is LocalValue local ? new ManagedAssignment(address, local, value) : new ManagedStore(address, target, value);
    /// <summary>写入标量帧区域（局部变量）：赋值。</summary>
    [StoreTargetRule(1)]
    internal static RecoveryResult<bool> StoreScalarFrame(this LoweringScope ctx, Store store, ManagedValue target, List<ManagedStatement> output)
    {
        if (target is not LocalValue local)
            return false;
        if (!ctx.Values.RecoverAs(store.Value, local.Type, store.Address).TryGet(out var value, out var failure))
            return failure;
        output.Add(new ManagedAssignment(store.Address, local, value));
        return true;
    }

    [CallRule(10)]
    internal static RecoveryResult<bool> BoxFrame(this LoweringScope ctx, Call call, List<ManagedStatement> output)
    {
        if (call is not { Op: { Kind: OpKind.Box, Operand: TypeRef type }, Arguments: [_, var data] } || ctx.types.Kind(type) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double) || ctx.Values.FrameAccess(data) is null)
            return false;
        if (type is DefinitionRef { Definition.FullName: "System.Nullable" })
            return RecoveryDiagnostics.Fail(call.Address, "装箱 Nullable 栈值尚未支持", rule: "BoxFrame");
        if (call.Defines.FirstOrDefault() is not { } created)
            return RecoveryDiagnostics.Fail(call.Address, "装箱 缺少结果变量", rule: "BoxFrame");
        if (!ctx.Values.StructAddress(data, type).TryGet(out var address, out var failure))
            return failure;
        var value = address is AddressValue a ? a.Target : new IndirectValue(address, type);
        if (ctx.Values.Assign(call.Address, created, () => new BoxValue(value, type, ctx.types.Object), output) is { } assignmentFailure)
            return assignmentFailure;
        return true;
    }

    /// <summary>CLR 的 initlocals 不是原生帧初值证据；每次读叶子/传址之前必须在所有正常前驱上已定义，异常入口不继承普通回边的初值。</summary>
    [BodyProof(30)]
    internal static void ProveFrameInitialization(this RecoveryScope ctx, ManagedBody body)
    {
        if (ctx.State.Frames.frameRegions.Count == 0)
            return;
        // 与读写重组使用相同的叶子布局，重叠整数别名不另占一份初始化状态。
        var all = ctx.State.Frames.frameRegions.SelectMany(r => ctx.ScalarStructPaths(r.Type).Select(p => ctx.PathValue(r.Local, p.Path))).ToHashSet();
        HashSet<ManagedValue> Under(ManagedValue value)
        {
            if (value is AddressValue a)
                return Under(a.Target);
            if (value is IndirectValue i)
                return Under(i.Address);
            if (all.Contains(value))
                return [value];
            if (ctx.types.Kind(value.Type) != TypeKind.Struct)
                return [];
            return ctx.ScalarStructPaths(value.Type).Select(p => ctx.PathValue(value, p.Path)).Where(all.Contains).ToHashSet();
        }

        foreach (var address in FrameInitialization.Uninitialized(body, all, Under))
            ctx.Hole(address, "栈 结构体叶子未在所有路径初始化", rule: "ProveFrameInitialization");
    }
}
