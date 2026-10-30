using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class FrameCopiesRules
{
    internal static RecoveryResult<CopyRange[]> CopyRanges(this RecoveryScope ctx, Expr address, int width)
    {
        var ranges = new List<CopyRange>();
        if (ctx.ArrayLocation(address) is { } element && ctx.types.Kind(element.Type.Element) == TypeKind.Struct && element.Offset + width / 8 <= ctx.types.Size(element.Type.Element))
        {
            if (!ctx.Recover(element.Array, null).TryGet(out var array, out var failure))
                return failure;
            if (!ctx.Index(element.Index).TryGet(out var index, out failure))
                return failure;
            var item = new ArrayElementValue(array, index, element.Type.Element, 0);
            ranges.Add(new(element.Type.Element, new AddressValue(item), element.Offset));
            foreach (var path in ctx.StructPaths(item.Type).Where(p => ctx.types.Kind(p.Type) == TypeKind.Struct && p.Offset <= element.Offset && element.Offset + width / 8 <= p.Offset + ctx.types.Size(p.Type)))
                ranges.Add(new(path.Type, new AddressValue(ctx.PathValue(item, path.Path)), element.Offset - path.Offset));
            return ranges.ToArray();
        }

        var (root, offset, rest) = ctx.Split(address);
        if (root is Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef owner } && rest.Count == 0 && ctx.facts.Layouts.Of(owner) is { } layout)
        {
            // 静态字段中的结构体：静态数据没有对象头，偏移直接是字段偏移。
            foreach (var slot in layout.Statics.Where(s => ctx.types.Kind(s.Type) == TypeKind.Struct && s.Offset <= offset && offset + width / 8 <= s.Offset + ctx.types.Size(s.Type)))
            {
                var field = new StaticFieldValue(new FieldRef(slot.Field, owner), slot.Type, 0);
                ranges.Add(new(slot.Type, new AddressValue(field), (int)offset - slot.Offset));
                foreach (var path in ctx.StructPaths(slot.Type).Where(p => ctx.types.Kind(p.Type) == TypeKind.Struct && slot.Offset + p.Offset <= offset && offset + width / 8 <= slot.Offset + p.Offset + ctx.types.Size(p.Type)))
                    ranges.Add(new(path.Type, new AddressValue(ctx.PathValue(field, path.Path)), (int)offset - slot.Offset - path.Offset));
            }

            return ranges.ToArray();
        }

        if (root is null || rest.Count != 0 || ctx.TypeOfAddressBase(root) is not { } type)
            return ranges.ToArray();
        if (!ctx.Recover(root, null).TryGet(out var value, out _))
            return ranges.ToArray();
        if (type is ByRefRef reference && ctx.types.Kind(reference.Element) == TypeKind.Struct && offset >= 0 && offset + width / 8 <= ctx.types.Size(reference.Element))
            ranges.Add(new(reference.Element, value, (int)offset));
        foreach (var path in ctx.StructPaths(type).Where(p => ctx.types.Kind(p.Type) == TypeKind.Struct && p.Offset <= offset && offset + width / 8 <= p.Offset + ctx.types.Size(p.Type)))
            ranges.Add(new(path.Type, new AddressValue(ctx.PathValue(value, path.Path)), (int)offset - path.Offset));
        return ranges.ToArray();
    }

    /// <summary>
    /// 结构体内的清零（例如 <c>this.&lt; &gt;u__1 = default</c> 编译成两个 64 位零写入，第二个覆盖 token 与其后的填充）：
    /// 写入范围落在同一个结构体值之内、只覆盖完整的叶子与填充时，逐叶子写零。填充不是托管值（ECMA-335 I.8.2.1），对照器也不比较它。
    /// </summary>
    [StoreRule(15)]
    internal static RecoveryResult<bool> StoreStructZero(this LoweringScope ctx, Store store, List<ManagedStatement> output)
    {
        if (!ctx.Values.FrameZero(store.Value) || ctx.Values.FrameAccess(store.Target) is not null || store.Value.Width < 16)
            return false;
        var width = store.Value.Width;
        if (!ctx.Values.CopyRanges(store.Target, width).TryGet(out var ranges, out var failure))
            return failure;
        var range = ranges.OrderBy(r => ctx.types.Size(r.Type)).FirstOrDefault();
        if (range is null)
            return false;
        var leaves = ctx.Values.StructPaths(range.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && p.Offset < range.Offset + width / 8 && range.Offset < p.Offset + ctx.types.Size(p.Type)).ToArray();
        if (leaves.Length == 0 || leaves.Any(p => p.Offset < range.Offset || p.Offset + ctx.types.Size(p.Type) > range.Offset + width / 8))
            return false;
        // 恰好是单个叶子的写入走普通路径。
        if (leaves is [var single] && single.Offset == range.Offset && ctx.types.Size(single.Type) * 8 == width)
            return false;
        // 清零恰好覆盖一个结构体位置（如状态机末尾的 <>u__1 = default）：整体 initobj，不逐叶子写私有字段。
        if (ctx.Values.WholeStructAt(range, width) is { } whole)
        {
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
            return true;
        }

        foreach (var leaf in leaves)
        {
            var target = ctx.Values.PathValue(range.Root, leaf.Path);
            output.Add(new ManagedStore(store.Address, target, ctx.types.Kind(leaf.Type) == TypeKind.Reference ? new ConstantValue(0, leaf.Type, 64) : new ConstantValue(0, leaf.Type, target.Width)));
        }

        return true;
    }

    /// <summary>
    /// 写入覆盖整个结构体字段，且写入的是同类型结构体值的对应叶子（单叶子结构体，如 this._ctx = ct，CancellationToken 只有私有字段 _source）：
    /// 写成整体赋值，不逐叶子写私有字段。
    /// </summary>
    [StoreTargetRule(5)]
    internal static bool StoreWholeStruct(this LoweringScope ctx, Store store, ManagedValue target, List<ManagedStatement> output)
    {
        // 写入目标：结构体字段本身，或结构体字段的唯一叶子；结构体大小等于写入宽度。由外向内是同大小的各层（如 <>u__1 与它的只读字段 task）。
        var candidates = new List<ManagedValue>();
        // 多叶子的写入目标（片）：各片都是同一个结构体位置的直接叶子时，从这个位置开始。
        ManagedValue? Outer(ManagedValue leaf) => leaf is FieldValue { Receiver: AddressValue { Target: var outer } } ? outer : null;
        var start = ctx.types.Kind(target.Type) == TypeKind.Struct ? target : target is Fragment pieces ? (pieces.Parts.Select(p => Outer(p.Value)).Distinct().ToArray() is [var common] ? common : null) : Outer(target);
        for (var layer = start; layer is not null && ctx.types.Kind(layer.Type) == TypeKind.Struct && ctx.types.Size(layer.Type) * 8 == store.Value.Width; layer = layer is FieldValue { Receiver: AddressValue { Target: var next } } ? next : null)
            candidates.Insert(0, layer);
        if (candidates.Count == 0)
            return false;
        var whole = candidates[0];
        // 写入零：default(T)（initobj），不写私有叶子（如状态机末尾的 <ct>5__2 = default）。
        if (ctx.Values.FrameZero(store.Value))
        {
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
            return true;
        }

        if (!ctx.Values.Recover(store.Value, null).TryGet(out var source, out _))
            return false;
        // 写入的值：同类型结构体值的叶子（单叶子），或各片都是同一个结构体值的叶子（寄存器传递的结构体参数/结果）。
        var parts = source is Fragment fragment ? fragment.Parts.Select(p => p.Value).ToArray() : [source];
        foreach (var layer in candidates)
        {
            var roots = parts.Select(p => FrameCopiesRules.StructRootOf(p, layer.Type)).Distinct().ToArray();
            if (roots is not [{ } value])
                continue;
            output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(layer), layer.Type), value));
            return true;
        }

        return false;
    }

    internal static ManagedBody RewriteAwaiters(this RecoveryScope ctx, ManagedBody body)
    {
        var changed = false;
        var blocks = body.Blocks.Select(block =>
        {
            var statements = new List<ManagedStatement>();
            foreach (var statement in block.Statements)
            {
                if (statement is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: var layer } }, Value: var task } store && ctx.AwaiterOf(store.Address, layer, task, statements))
                {
                    changed = true;
                    continue;
                }

                statements.Add(statement);
            }

            return block with
            {
                Statements = statements
            };
        }).ToArray();
        return changed ? body with
        {
            Blocks = blocks
        }

        : body;
    }

    internal static bool AwaiterOf(this RecoveryScope ctx, ulong address, ManagedValue layer, ManagedValue task, List<ManagedStatement> output)
    {
        if (layer is not FieldValue { Field: { Field.Name: "task" } field, Receiver: AddressValue { Target: var awaiter } } || (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) == 0 || awaiter.Type is not DefinitionRef { Definition: { Name: "Awaiter", DeclaringType.FullName: "Cysharp.Threading.Tasks.UniTask" } } || task.Type is not DefinitionRef { Definition.FullName: "Cysharp.Threading.Tasks.UniTask", Arguments: [_] } unitask || unitask.Definition.Methods.FirstOrDefault(m => m is { Name: "GetAwaiter", IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }) is not { } getAwaiter)
            return false;
        ManagedValue? receiver = task switch
        {
            LocalValue or FieldValue or ArgumentValue => new AddressValue(task),
            IndirectValue indirect => indirect.Address,
            _ => null,
        };
        if (receiver is null)
            return false;
        var result = awaiter as LocalValue ?? ctx.StructLocal(awaiter.Type, 0);
        output.Add(new ManagedCall(address, new ManagedInvocation(new MethodRef(getAwaiter, unitask.Arguments, []), receiver, [], false), result, false) { Inlined = true });
        if (!ReferenceEquals(result, awaiter))
            output.Add(new ManagedStore(address, new IndirectValue(new AddressValue(awaiter), awaiter.Type), result));
        return true;
    }

    internal static ManagedValue? WholeStructAt(this RecoveryScope ctx, CopyRange range, int width)
    {
        if (ctx.types.Kind(range.Type) == TypeKind.Struct && range.Offset == 0 && ctx.types.Size(range.Type) * 8 == width)
            return range.Root is AddressValue address ? address.Target : new IndirectValue(range.Root, range.Type);
        var path = ctx.StructPaths(range.Type).Where(p => p.Offset == range.Offset && ctx.types.Kind(p.Type) == TypeKind.Struct && ctx.types.Size(p.Type) * 8 == width).OrderBy(p => p.Path.Length).FirstOrDefault();
        return path.Path is null ? null : ctx.PathValue(range.Root, path.Path);
    }

    /// <summary>叶子值的结构体根（逐层剥去字段与取址，直到类型为 type）。</summary>
    internal static ManagedValue? StructRootOf(ManagedValue leaf, TypeRef type)
    {
        for (var value = leaf; value is not null;)
        {
            if (value.Type.Equals(type))
                return value;
            value = value switch
            {
                FieldValue f => f.Receiver is AddressValue a ? a.Target : f.Receiver,
                AddressValue a => a.Target,
                _ => null,
            };
        }

        return null;
    }

    [Analysis("帧拷贝", 110, After = ["类型"])]
    internal static RecoveryFailure? FrameCopies(this RecoveryScope ctx)
    {
        if (!ctx.PrepareFrameCopies().TryGet(out _, out var failure))
            return failure;
        if (ctx.PrepareStructZeroes() is { } zeroFailure)
            return zeroFailure;
        ctx.PrepareFrameZeroes();
        ctx.PrepareStoredResults();
        return null;
    }

    internal static void PrepareFrameZeroes(this RecoveryScope ctx)
    {
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var run = new List<(Store Store, FrameRegion Region, long Offset)>();
                for (var j = i; j < block.Statements.Count && block.Statements[j] is Store s && !ctx.State.Frames.frameCopies.ContainsKey(s) && ctx.FrameZero(s.Value) && ctx.FrameAccess(s.Target) is { } access; j++)
                    run.Add((s, access.Region, access.Offset));
                if (run.Count == 0)
                    continue;
                foreach (var group in run.GroupBy(r => r.Region))
                {
                    var region = group.Key;
                    if (ctx.types.Kind(region.Type) != TypeKind.Struct || group.Any(r => r.Offset < 0 || r.Offset + r.Store.Value.Width / 8 > region.Size))
                        continue;
                    var covered = group.SelectMany(r => Enumerable.Range((int)r.Offset, r.Store.Value.Width / 8)).ToHashSet();
                    if (ctx.StructPaths(region.Type).Any(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && Enumerable.Range(p.Offset, ctx.types.Size(p.Type)).Any(b => !covered.Contains(b))))
                        continue;
                    var first = group.First().Store;
                    ctx.State.Frames.frameCopies[first] = [new ManagedStore(first.Address, new IndirectValue(new AddressValue(region.Local), region.Type), new ComposedValue(region.Type, []))];
                    foreach (var other in group.Skip(1))
                        ctx.State.Frames.frameCopies[other.Store] = [];
                }

                i += run.Count - 1;
            }
    }

    internal static RecoveryFailure? PrepareStructZeroes(this RecoveryScope ctx)
    {
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (ctx.State.Frames.frameCopies.ContainsKey(block.Statements[i]) || block.Statements[i] is not Store first || !ctx.FrameZero(first.Value) || ctx.FrameAccess(first.Target) is not null)
                    continue;
                var run = new List<Store>();
                for (var j = i; j < block.Statements.Count && block.Statements[j] is Store s && ctx.FrameZero(s.Value) && ctx.FrameAccess(s.Target) is null && !ctx.State.Frames.frameCopies.ContainsKey(s); j++)
                    run.Add(s);
                if (run.Count < 2)
                    continue;
                var ranges = new List<CopyRange[]>();
                foreach (var store in run)
                {
                    if (!ctx.CopyRanges(store.Target, store.Value.Width).TryGet(out var candidates, out var failure))
                        return failure;
                    ranges.Add(candidates);
                }

                // 候选是第一条写入所在的结构体值（从外到内）；每条写入都须落在其中，并合起来覆盖它的全部叶子。
                foreach (var whole in ranges[0].Where(r => r.Offset == 0).OrderByDescending(r => ctx.types.Size(r.Type)))
                {
                    var size = ctx.types.Size(whole.Type);
                    var covered = new HashSet<int>();
                    var count = 0;
                    foreach (var (store, candidates) in run.Zip(ranges))
                    {
                        if (candidates.FirstOrDefault(r => r.Type.Equals(whole.Type) && r.Root.Equals(whole.Root)) is not { } inner || inner.Offset + store.Value.Width / 8 > size)
                            break;
                        for (var k = 0; k < store.Value.Width / 8; k++)
                            covered.Add(inner.Offset + k);
                        count++;
                    }

                    if (count < 2 || ctx.StructPaths(whole.Type).Any(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null) && Enumerable.Range(p.Offset, ctx.types.Size(p.Type)).Any(b => !covered.Contains(b))))
                        continue;
                    ctx.State.Frames.frameCopies[run[0]] = [new ManagedStore(run[0].Address, new IndirectValue(whole.Root, whole.Type), new ComposedValue(whole.Type, []))];
                    foreach (var store in run.Skip(1).Take(count - 1))
                        ctx.State.Frames.frameCopies[store] = [];
                    i += count - 1;
                    break;
                }
            }

        return null;
    }

    internal static void PrepareStoredResults(this RecoveryScope ctx)
    {
        (ManagedValue Root, AbiPiece Piece, AbiPiece[] Pieces)? Source(Use use)
        {
            if (use.Variable.Version == 0 && ctx.State.Signature.structArguments.TryGetValue(use.Variable.Storage, out var argument))
                return (argument.Root, argument.Piece, ctx.State.Signature.structArguments.Values.Where(a => a.Root.Equals(argument.Root)).Select(a => a.Piece).ToArray());
            if (!ctx.results.TryGetValue(use.Variable, out var result) || ctx.Resolve(result.Call) is not { } callee
                || ctx.owner.abi.Classify(callee, out _)?.Return is not { } returned || !ctx.RegisterStruct(returned)
                || returned.Pieces.FirstOrDefault(p => p.Register == result.Call.Results[result.Index]) is not { } piece)
                return null;
            return (ctx.CallStructLocal(result.Call, returned.Type), piece, returned.Pieces);
        }

        CopyRange[] Ranges(Store store) => ctx.FrameAccess(store.Target) is { } access
            ? [new(access.Region.Type, new AddressValue(access.Region.Local), (int)access.Offset)]
            : ctx.CopyRanges(store.Target, store.Value.Width).TryGet(out var ranges, out _) ? ranges : [];

        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Store { Value: Use first } store || ctx.State.Frames.frameCopies.ContainsKey(store)
                    || Source(first) is not { } source || Ranges(store).FirstOrDefault(r => r.Type.Equals(source.Root.Type) && r.Offset == source.Piece.Offset) is not { } target)
                    continue;
                var pieces = new List<Store>();
                var offsets = new HashSet<int>();
                for (var j = i; j < block.Statements.Count && pieces.Count < source.Pieces.Length; j++)
                {
                    if (block.Statements[j] is not Store { Value: Use piece } next || ctx.State.Frames.frameCopies.ContainsKey(next)
                        || Source(piece) is not { } copied || !copied.Root.Equals(source.Root) || copied.Piece.Width != next.Value.Width
                        || !Ranges(next).Any(r => r.Type.Equals(target.Type) && r.Root.Equals(target.Root) && r.Offset == copied.Piece.Offset)
                        || !offsets.Add(copied.Piece.Offset))
                        break;
                    pieces.Add(next);
                }

                if (pieces.Count != source.Pieces.Length || !offsets.SetEquals(source.Pieces.Select(p => p.Offset)))
                    continue;
                // 参数与调用结果都是稳定值；完整同偏移写入可直接复制到栈、字段或数组元素。
                ctx.State.Frames.frameCopies[pieces[0]] = [new ManagedStore(pieces[0].Address, new IndirectValue(target.Root, target.Type), source.Root)];
                foreach (var piece in pieces.Skip(1))
                    ctx.State.Frames.frameCopies[piece] = [];
                i += pieces.Count - 1;
            }
    }

    /// <summary>帧区域之间的整体拷贝替代原来的逐字访存。</summary>
    [StatementRule(10)]
    internal static bool LowerFrameCopy(this LoweringScope ctx, Block block, Stmt statement, List<ManagedStatement> output)
    {
        if (!ctx.State.Frames.frameCopies.TryGetValue(statement, out var copy))
            return false;
        output.AddRange(copy);
        return true;
    }

    /// <summary>拷贝中的一段读取：整体读取，或窄读取零扩展到寄存器（写入时再取回原宽度，如 20 字节结构体的末 4 字节）。</summary>
    internal static Load? CopiedLoad(Expr value) => value switch
    {
        Load load => load,
        Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: Load { Width: 32 or 16 or 8 } inner } => inner,
        _ => null,
    };
    internal static RecoveryResult<bool> PrepareFrameCopies(this RecoveryScope ctx)
    {
        var statements = ctx.blocks.SelectMany(b => b.Statements).ToArray();
        var uses = new Dictionary<Variable, List<Stmt>>();
        foreach (var statement in statements)
        {
            // 间接返回由 x8 指向的完整缓冲区决定，L2 的返回寄存器不参与托管返回值。
            if (statement is Return && ctx.State.Signature.ownReturnBuffer is not null)
                continue;
            var variables = statement is Phi phi ? phi.Sources : ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
            foreach (var variable in variables)
            {
                if (!uses.TryGetValue(variable, out var list))
                    uses[variable] = list = [];
                list.Add(statement);
            }
        }

        var copies = new List<FrameCopy>();
        foreach (var define in statements.OfType<Define>())
        {
            if (FrameCopiesRules.CopiedLoad(define.Value) is not { Width: 64 or 128 or 32 } load || !uses.TryGetValue(define.Target, out var users) || users is not [Store { Value: Use use } store] || use.Width != load.Width || ctx.State.Lowering.dropped.Contains(store))
                continue;
            // 至少一端是栈结构体根时可以逐叶子拷贝；两端都不在栈上时，只接受下面合并成的整体拷贝（覆盖整个结构体）。
            var onFrame = ctx.FrameAccess(load.Address) is not null || ctx.FrameAccess(store.Target) is not null;
            if (!ctx.CopyRanges(load.Address, load.Width).TryGet(out var sources, out var failure))
                return failure;
            if (!ctx.CopyRanges(store.Target, load.Width).TryGet(out var targets, out failure))
                return failure;
            var pairs = (
                from source in sources
                from target in targets
                where source.Type.Equals(target.Type) && source.Offset == target.Offset
                orderby ctx.types.Size(source.Type) descending
                select (source, target)).ToArray();
            if (pairs.Length == 0)
                continue;
            // 先使用两端共有的最外层类型，连续分片才能一起覆盖包含嵌套结构体的完整值。
            var outermost = pairs.Where(p => ctx.types.Size(p.source.Type) == ctx.types.Size(pairs[0].source.Type)).Distinct().ToArray();
            // 同样大小、在同一偏移互相嵌套的结构体（例如 UniTask.Awaiter 只有一个 UniTask 字段）覆盖相同的叶子，取最外层，逐叶子拷贝的结果相同。
            if (outermost.Length > 1)
                outermost = outermost.Where(p => outermost.All(q => q == p || ctx.StructPaths(p.source.Type).Any(path => path.Offset == 0 && path.Type.Equals(q.source.Type)))).ToArray();
            if (outermost.Length != 1)
                continue;
            var (from, to) = outermost[0];
            if (from.Type is GenericParameterRef { NativeAggregate: not null })
            {
                // 开放 T 没有可访问的实例字段；只允许后续完整覆盖检查把所有片合并成一次复制。
                copies.Add(new FrameCopy(define, store, from, to, new Fragment([], ctx.types.UInt64, load.Width)));
                continue;
            }

            var paths = ctx.StructPaths(from.Type).Where(p => ctx.types.Kind(p.Type) is not (TypeKind.Struct or null)).OrderBy(p => p.Offset).ToArray();
            var touched = paths.Where(p => p.Offset < from.Offset + load.Width / 8 && from.Offset < p.Offset + ctx.types.Size(p.Type)).ToArray();
            if (touched.Length == 0 || touched.Any(p => p.Offset < from.Offset || p.Offset + ctx.types.Size(p.Type) > from.Offset + load.Width / 8))
                continue;
            if (touched.Zip(touched.Skip(1)).Any(p => p.First.Offset + ctx.types.Size(p.First.Type) > p.Second.Offset))
                continue;
            var snapshot = new Fragment(touched.Select(p => new Part((p.Offset - from.Offset) * 8, ctx.StructLocal(p.Type, ctx.types.Size(p.Type) * 8))).ToArray(), ctx.types.UInt64, load.Width);
            var copy = new FrameCopy(define, store, from, to, snapshot);
            copies.Add(copy);
            if (!onFrame)
                continue;
            ctx.State.Frames.frameCopies[define] = touched.Select((p, i) => (ManagedStatement)new ManagedAssignment(define.Address, (LocalValue)snapshot.Parts[i].Value, ctx.PathValue(from.Root, p.Path))).ToArray();
            ctx.State.Frames.frameCopies[store] = touched.Select((p, i) => (ManagedStatement)new ManagedStore(store.Address, ctx.PathValue(to.Root, p.Path), snapshot.Parts[i].Value)).ToArray();
        }

        // 完整复制仅在“先读完、后写入”的连续序列中合并，跨调用/未知访存不得移动快照。
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var first = copies.FirstOrDefault(c => ReferenceEquals(c.Load, block.Statements[i]));
                if (first is null)
                    continue;
                var sequence = new List<FrameCopy>();
                var start = i;
                while (i < block.Statements.Count && copies.FirstOrDefault(c => ReferenceEquals(c.Load, block.Statements[i])) is { } next && next.Source.Type.Equals(first.Source.Type) && next.Source.Root.Equals(first.Source.Root) && next.Target.Root.Equals(first.Target.Root))
                {
                    sequence.Add(next);
                    i++;
                }

                var stores = block.Statements.Skip(i).Take(sequence.Count).ToArray();
                if (stores.Length != sequence.Count || !sequence.All(c => stores.Any(s => ReferenceEquals(s, c.Store))))
                {
                    i = start;
                    continue;
                }

                var intervals = sequence.OrderBy(c => c.Source.Offset).ToArray();
                var cursor = 0;
                foreach (var copy in intervals)
                {
                    if (copy.Source.Offset != cursor)
                    {
                        cursor = -1;
                        break;
                    }

                    cursor += copy.Snapshot.Width / 8;
                }

                if (cursor != ctx.types.Size(first.Source.Type))
                {
                    i = start;
                    continue;
                }

                var value = ctx.StructLocal(first.Source.Type, 0);
                foreach (var copy in sequence)
                {
                    ctx.State.Frames.frameCopies[copy.Load] = [];
                    ctx.State.Frames.frameCopies[copy.Store] = [];
                }

                ctx.State.Frames.frameCopies[first.Load] = [new ManagedAssignment(first.Load.Address, value, new IndirectValue(first.Source.Root, first.Source.Type))];
                var last = (Store)stores[^1];
                ctx.State.Frames.frameCopies[last] = [new ManagedStore(last.Address, new IndirectValue(first.Target.Root, first.Target.Type), value)];
                i += stores.Length - 1;
            }

        return copies.Count != 0;
    }
}
