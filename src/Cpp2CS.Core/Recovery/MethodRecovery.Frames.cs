using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record FrameRegion(long Offset, TypeRef Type, int Size, LocalValue Local);
        private sealed record FrameWitness(long Offset, TypeRef Type, Stmt Call, bool Writes);
        // 只在 L3 内使用的地址见证；保留区域身份，后续栈着色不会把两个局部变量混为一体。
        private sealed record TypedFrame(FrameRegion Region) : Expr(64);
        private readonly List<FrameRegion> frameRegions = [];
        private readonly HashSet<long> conflictingFrames = [];
        private readonly Dictionary<FrameRegion, HashSet<Stmt>> frameLives = [];
        private readonly Dictionary<Stmt, ManagedStatement[]> frameInitializers = new(ReferenceEqualityComparer.Instance);

        private bool ContainsFrameType(FrameRegion outer, long offset, TypeRef type) =>
            outer.Offset == offset && outer.Type.Equals(type)
            || StructPaths(outer.Type).Any(p => outer.Offset + p.Offset == offset && p.Type.Equals(type));

        /// <summary>先解析接收者及虚调用返回类型，避免帧区域只看见直调签名而提前固定错误的栈槽类型。</summary>
        [Analysis("帧前类型", 29, After = ["异常值", "栈上调用"])]
        private void PrepareFrameTypes() => InferTypes();

        /// <summary>只有精确调用签名提供类型；普通访存宽度不能定型。异型重叠先拒绝，嵌套字段见证合并到外根。</summary>
        [Analysis("帧区域", 30, After = ["异常值", "栈上调用", "帧前类型"])]
        private void PrepareFrames()
        {
            var witnesses = new List<FrameWitness>();
            void Bind(Expr expression, TypeRef type, Call call, bool writes = false)
            {
                // 结构体，以及按地址传递的基元/引用（基元值类型实例方法的 this，如 x.ToString()；out/ref 参数）：后者是一个该类型的局部变量。
                if (types.Kind(type) is TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Reference
                    && FrameOffset(expression) is { } offset && types.Size(type) > 0)
                    witnesses.Add(new(offset, type, call, writes));
            }
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (stackEnums.ContainsKey(call)) continue;
                if (!call.Arguments.Any(argument => FrameOffset(argument) is not null)) continue;
                // 装箱提供精确值类型；标量的到达写入划出生命期，允许后续结构体复用同一物理槽。
                if (call.Op is { Kind: OpKind.Box, Operand: TypeRef boxedType } && call.Arguments.LastOrDefault() is { } data
                    && types.Kind(boxedType) is TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)
                {
                    Bind(data, boxedType, call);
                    if (types.Kind(boxedType) != TypeKind.Struct && FrameOffset(data) is { } offset)
                    {
                        var block = blocks.Single(b => b.Statements.Contains(call));
                        if (ReachingStackStore(block, block.Statements.IndexOf(call), offset, [], types.Size(boxedType) * 8) is { } store)
                            witnesses.Add(new(offset, boxedType, store, true));
                    }
                }
                if (Resolve(call) is not { } callee || owner.abi.Classify(callee, out _) is not { } signature) continue;
                // 帧区域按这次解析的签名定型；之后类型变化也不能换成另一个 ICF 候选，否则区域类型与调用不一致。
                resolved[call] = (callee, Pinned);
                var registers = ArgumentsOf(call);
                foreach (var argument in signature.Arguments.Concat(signature.Return is { Passing: Passing.Indirect } ret ? [ret] : []))
                {
                    if (argument.Pieces.Length != 1 || !registers.TryGetValue(argument.Pieces[0].Register, out var expression)) continue;
                    if (argument.Type is ByRefRef reference) Bind(expression, reference.Element, call);
                    else if (argument.Passing == Passing.Indirect) Bind(expression, argument.Type, call, ReferenceEquals(argument, signature.Return));
                }
            }
            WitnessStoredResults(witnesses);
            WitnessFrameCopies(witnesses);
            var regions = witnesses.DistinctBy(w => (w.Offset, w.Type)).Select(w => new FrameRegion(w.Offset, w.Type, types.Size(w.Type), StructLocal(w.Type, ScalarWidth(w.Type))))
                .OrderByDescending(r => r.Size).ThenBy(r => r.Offset).ToArray();
            foreach (var region in regions)
            {
                if (regions.Any(other => other != region && region.Offset < other.Offset + other.Size && other.Offset < region.Offset + region.Size
                    && !ContainsFrameType(region, other.Offset, other.Type) && !ContainsFrameType(other, region.Offset, region.Type)))
                {
                    conflictingFrames.Add(region.Offset);
                    continue;
                }
                if (!frameRegions.Any(outer => ContainsFrameType(outer, region.Offset, region.Type))) frameRegions.Add(region);
            }
            PrepareColoredFrames(regions, witnesses);
            foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var old = block.Statements[i];
                if (stackEnumStorage.Contains(old)) continue;
                var mapped = ExprMap.MapOperands(old, e => ExprMap.Map(e, part =>
                {
                    if (FrameOffset(part) is not { } offset) return null;
                    // 同一处落在多个区域（生命期拆分不完整）：不绑定，留给栈槽类型冲突报洞。
                    var matching = frameRegions.Where(r => offset >= r.Offset && offset < r.Offset + r.Size
                        && (!frameLives.TryGetValue(r, out var live) || live.Contains(old))).Take(2).ToArray();
                    if (matching is not [var region])
                    {
                        if (matching.Length > 1) conflictingFrames.Add(offset);
                        return null;
                    }
                    Expr root = new TypedFrame(region);
                    return offset == region.Offset ? root : new Binary(BinOp.Add, root, new Const((ulong)(offset - region.Offset), 64), 64);
                }));
                if (ReferenceEquals(old, mapped)) continue;
                // 若隐藏槽同时属于托管区域，其写入也有字段语义，不能仅作为调用元数据删去。
                dropped.Remove(old);
                block.Statements[i] = mapped;
                ledger.Replace(old, mapped);
                if (mapped is Call call && resolved.Remove((Call)old, out var target)) resolved[call] = target;
            }
            // IR 改写后，定义索引按新语句重建。
            definitions = IndexDefinitions();
            PrepareFrameInitializers();
        }

        /// <summary>
        /// 寄存器返回的结构体按 ABI 片原样写入相邻栈槽（每片恰好一次写入、偏移差等于片偏移）：这段栈就是一个该类型的值，
        /// 例如 GetAwaiter 内联时把返回的 UniTask 存进临时 awaiter。类型来自被调用者的签名，与参数见证同一依据。
        /// </summary>
        private void WitnessStoredResults(List<FrameWitness> witnesses)
        {
            var stores = blocks.SelectMany(b => b.Statements).OfType<Store>()
                .Select(s => (Store: s, Offset: s.Value is Use ? FrameOffset(s.Target) : null)).Where(p => p.Offset is not null)
                .ToLookup(p => ((Use)p.Store.Value).Variable);
            if (stores.Count == 0) return;
            foreach (var call in blocks.SelectMany(b => b.Statements).OfType<Call>())
            {
                if (!call.Defines.Any(d => d is not null && stores.Contains(d))) continue;
                if (Resolve(call) is not { } callee || owner.abi.Classify(callee, out _)?.Return is not { } returned || !RegisterStruct(returned)) continue;
                long? origin = null;
                foreach (var piece in returned.Pieces)
                {
                    var index = Array.IndexOf(call.Results, piece.Register);
                    var written = index >= 0 && index < call.Defines.Length && call.Defines[index] is { } defined
                        ? stores[defined].Where(p => p.Store.Value.Width == piece.Width).Select(p => p.Offset!.Value - piece.Offset).ToArray() : [];
                    if (written is not [var at] || origin is not null && origin != at) { origin = null; break; }
                    origin = at;
                }
                if (origin is not { } offset) continue;
                resolved[call] = (callee, Pinned);
                witnesses.Add(new(offset, returned.Type, call, false));
            }
            // 结构体值的整体读取（静态字段、对象或 ByRef 根上的结构体字段）原样写入栈槽：例如 await UniTask.CompletedTask 把静态字段拷进临时 awaiter。
            foreach (var group in stores)
            {
                if (!values.TryGetValue(group.Key, out var value) || value is not Load { Width: 64 or 128 } load) continue;
                var ranges = CopyRanges(load.Address, load.Width).Where(r => r.Offset == 0 && types.Size(r.Type) * 8 == load.Width).ToArray();
                var outer = ranges.Where(r => ranges.All(q => q == r || StructPaths(r.Type).Any(p => p.Offset == 0 && p.Type.Equals(q.Type)))).Select(r => r.Type).Distinct().ToArray();
                if (outer is not [var type]) continue;
                foreach (var (store, offset) in group)
                    if (store.Value.Width == load.Width) witnesses.Add(new(offset!.Value, type, store, false));
            }
        }

        /// <summary>
        /// 栈区域之间的整体拷贝传递类型：一段栈与一个已定型的区域之间（任一方向）的逐段读写，各段相对偏移相同、合起来覆盖该类型的全部叶子时，
        /// 这段栈是同一类型的值（例如 UniTask&lt;T&gt; 经 x8 返回后被拷进临时区域，再拷进 awaiter）。迭代到不动点。
        /// </summary>
        private void WitnessFrameCopies(List<FrameWitness> witnesses)
        {
            var sites = blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i)))
                .Where(p => p.Statement is Define).ToDictionary(p => ((Define)p.Statement).Target);
            TypeRef? ReachingType(Variable value, long offset)
            {
                if (!sites.TryGetValue(value, out var site)) return null;
                var block = site.Block;
                var position = site.Index;
                var seen = new HashSet<Block>();
                while (seen.Add(block))
                {
                    foreach (var statement in block.Statements.Take(position).Reverse())
                    {
                        var writers = witnesses.Where(w => w.Offset == offset && ReferenceEquals(w.Call, statement) && (w.Writes || w.Call is Store))
                            .Select(w => w.Type).Distinct().ToArray();
                        if (writers.Length > 0) return writers is [var type] ? type : null;
                        if (statement is Call call && !IsWriteBarrier(call) && call.Arguments.Any(a => FrameOffset(a) == offset)) return null;
                    }
                    if (block.Predecessors.ToArray() is not [var parent] || parent.Handler == block) return null;
                    block = parent;
                    position = block.Statements.Count;
                }
                return null;
            }
            var copies = new List<(long From, long To, int Width, Stmt Store, Variable Value)>();
            foreach (var store in blocks.SelectMany(b => b.Statements).OfType<Store>())
                if (store.Value is Use { Variable: var v } use && values.TryGetValue(v, out var value) && CopiedLoad(value) is { Width: 64 or 128 or 32 } load
                    && load.Width == use.Width && FrameOffset(load.Address) is { } from && FrameOffset(store.Target) is { } to)
                    copies.Add((from, to, load.Width, store, v));
            if (copies.Count == 0) return;
            for (var round = 0; round < 8; round++)
            {
                var added = false;
                foreach (var known in witnesses.DistinctBy(w => (w.Offset, w.Type)).ToArray())
                {
                    var size = types.Size(known.Type);
                    var leaves = StructPaths(known.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).ToArray();
                    var ambiguous = witnesses.Any(w => w.Offset == known.Offset && !w.Type.Equals(known.Type)
                        && !StructPaths(known.Type).Any(p => p.Offset == 0 && p.Type.Equals(w.Type))
                        && !StructPaths(w.Type).Any(p => p.Offset == 0 && p.Type.Equals(known.Type)));
                    foreach (var forward in new[] { true, false })
                        foreach (var group in copies.Where(c => (forward ? c.From : c.To) >= known.Offset && (forward ? c.From : c.To) < known.Offset + size)
                            // 复用的源槽按本次读取前的完整写入定型，不能沿另一生命期的类型传播。
                            .Where(c => !forward || !ambiguous || known.Type.Equals(ReachingType(c.Value, known.Offset)))
                            .GroupBy(c => forward ? c.To - c.From : c.From - c.To))
                        {
                            var other = known.Offset + group.Key;
                            if (witnesses.Any(w => w.Offset == other && w.Type.Equals(known.Type))) continue;
                            // 明确来源的正向复制也可能覆盖一个已被复用的槽；保留新类型见证，交给生命期分析拆分。
                            // 反向传播不能覆盖调用签名；正向只使用本次读取已经确定的类型。
                            if (witnesses.Any(w => w.Offset == other) && !forward) continue;
                            var covered = new HashSet<long>();
                            foreach (var c in group)
                                for (var k = 0; k < c.Width / 8; k++) covered.Add((forward ? c.From : c.To) - known.Offset + k);
                            if (group.Any(c => (forward ? c.From : c.To) + c.Width / 8 > known.Offset + size)
                                || leaves.Any(p => Enumerable.Range(p.Offset, types.Size(p.Type)).Any(b => !covered.Contains(b)))) continue;
                            witnesses.Add(new(other, known.Type, group.First().Store, false));
                            added = true;
                        }
                }
                if (!added) break;
            }
        }

        /// <summary>标量帧区域的局部变量位宽（结构体为 0）。</summary>
        private int ScalarWidth(TypeRef type) => types.Kind(type) switch
        {
            TypeKind.Struct => 0,
            TypeKind.Bool => 8,
            TypeKind.Reference => 64,
            _ => types.Bits(type),
        };

        private bool FrameZero(Expr expression, HashSet<Variable>? active = null)
        {
            active ??= [];
            return expression switch
            {
                Const { Value: 0 } => true,
                Ir.Convert c => FrameZero(c.Operand, active),
                Insert i => FrameZero(i.Base, active) && FrameZero(i.Value, active),
                Use u when active.Add(u.Variable) && values.TryGetValue(u.Variable, out var value) => FrameZero(value, active),
                _ => false,
            };
        }

        /// <summary>同块连续零写入完整覆盖区域才合并；任何读取、调用或跨区域写入都截断证明。</summary>
        private void PrepareFrameInitializers()
        {
            foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Store first || FrameAccess(first.Target) is not { } start || !FrameZero(first.Value)) continue;
                var region = start.Region;
                var stores = new List<Store>();
                var covered = new HashSet<long>();
                for (var j = i; j < block.Statements.Count; j++)
                {
                    if (block.Statements[j] is not Store store || FrameAccess(store.Target) is not { } access || access.Region != region
                        || !FrameZero(store.Value) || access.Offset < 0 || access.Offset + store.Value.Width / 8 > region.Size) break;
                    stores.Add(store);
                    for (var k = 0; k < store.Value.Width / 8; k++) covered.Add(access.Offset + k);
                }
                if (covered.Count != region.Size) continue;
                frameInitializers[first] = types.Kind(region.Type) == TypeKind.Struct
                    ? [new ManagedStore(first.Address, new IndirectValue(new AddressValue(region.Local), region.Type), new ComposedValue(region.Type, []))]
                    : [new ManagedAssignment(first.Address, region.Local, new ConstantValue(0, region.Type, region.Local.Width))];
                foreach (var store in stores.Skip(1)) dropped.Add(store);
                i += stores.Count - 1;
            }
        }

        /// <summary>帧区域的初始化语句（清零、拷贝入）替代原语句。</summary>
        [StatementRule(20)]
        private bool LowerFrameInitializer(Block block, Stmt statement, List<ManagedStatement> output)
        {
            if (!frameInitializers.TryGetValue(statement, out var initialization)) return false;
            output.AddRange(initialization);
            return true;
        }

        [StoreRule(10)]
        private bool StoreFrameZero(Store store, List<ManagedStatement> output)
        {
            if (FrameAccess(store.Target) is not { } frame || !FrameZero(store.Value)) return false;
            // 一次清零覆盖相邻的多个帧区域（如两个 out float）：按区域逐个清零，每个区域须被完整覆盖。
            if (frame.Offset + store.Value.Width / 8 > frame.Region.Size)
            {
                var start = frame.Region.Offset + frame.Offset;
                var end = start + store.Value.Width / 8;
                var covered = frameRegions.Where(r => r.Offset < end && start < r.Offset + r.Size).OrderBy(r => r.Offset).ToArray();
                if (covered.Any(r => r.Offset < start || r.Offset + r.Size > end) || covered.Sum(r => (long)r.Size) != end - start) return false;
                foreach (var region in covered)
                {
                    var whole = FrameLocation(region, 0, region.Size * 8);
                    foreach (var leaf in whole is Fragment parts ? parts.Parts.Select(p => p.Value) : [whole])
                        output.Add(StoreTo(store.Address, leaf, new ConstantValue(0, leaf.Type, leaf.Width)));
                }
                return true;
            }
            // 不先把 q 零值强行缩成 ulong；按区域布局逐个验证完整覆盖的叶子。
            var location = FrameLocation(frame.Region, frame.Offset, store.Value.Width);
            foreach (var leaf in location is Fragment fragment ? fragment.Parts.Select(p => p.Value) : [location])
                output.Add(StoreTo(store.Address, leaf, new ConstantValue(0, leaf.Type, leaf.Width)));
            return true;
        }

        /// <summary>写入存储位置；标量帧区域本身是局部变量，写入即赋值。</summary>
        private static ManagedStatement StoreTo(ulong address, ManagedValue target, ManagedValue value) =>
            target is LocalValue local ? new ManagedAssignment(address, local, value) : new ManagedStore(address, target, value);

        /// <summary>写入标量帧区域（局部变量）：赋值。</summary>
        [StoreTargetRule(1)]
        private bool StoreScalarFrame(Store store, ManagedValue target, List<ManagedStatement> output)
        {
            if (target is not LocalValue local) return false;
            output.Add(new ManagedAssignment(store.Address, local, RecoverAs(store.Value, local.Type, store.Address)));
            return true;
        }

        [CallRule(10)]
        private bool BoxFrame(Call call, List<ManagedStatement> output)
        {
            if (call is not { Op: { Kind: OpKind.Box, Operand: TypeRef type }, Arguments: [_, var data] }
                || types.Kind(type) is not (TypeKind.Struct or TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double)
                || FrameAccess(data) is null) return false;
            if (type is DefinitionRef { Definition.FullName: "System.Nullable" }) throw Fail(call.Address, "装箱 Nullable 栈值尚未支持");
            if (call.Defines.FirstOrDefault() is not { } created) throw Fail(call.Address, "装箱 缺少结果变量");
            var address = StructAddress(data, type);
            var value = address is AddressValue a ? a.Target : new IndirectValue(address, type);
            output.Add(new ManagedAssignment(call.Address, Local(created), new BoxValue(value, type, types.Object)));
            return true;
        }

        /// <summary>CLR 的 initlocals 不是原生帧初值证据；每次读叶子/传址之前必须在所有正常前驱上已定义，异常入口不继承普通回边的初值。</summary>
        [BodyProof(30)]
        private void ProveFrameInitialization(ManagedBody body)
        {
            if (frameRegions.Count == 0) return;
            var all = frameRegions.SelectMany(r => StructPaths(r.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null))
                .Select(p => PathValue(r.Local, p.Path))).ToHashSet();
            HashSet<ManagedValue> Under(ManagedValue value)
            {
                if (value is AddressValue a) return Under(a.Target);
                if (value is IndirectValue i) return Under(i.Address);
                if (all.Contains(value)) return [value];
                if (types.Kind(value.Type) != TypeKind.Struct) return [];
                return StructPaths(value.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).Select(p => PathValue(value, p.Path)).Where(all.Contains).ToHashSet();
            }
            foreach (var address in FrameInitialization.Uninitialized(body, all, Under))
                Hole(address, "栈 结构体叶子未在所有路径初始化");
        }
    }
}
