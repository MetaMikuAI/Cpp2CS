using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record CopyRange(TypeRef Type, ManagedValue Root, int Offset);
        private sealed record FrameCopy(Define Load, Store Store, CopyRange Source, CopyRange Target, Fragment Snapshot);
        private readonly Dictionary<Stmt, ManagedStatement[]> frameCopies = new(ReferenceEqualityComparer.Instance);

        private RecoveryResult<CopyRange[]> CopyRanges(Expr address, int width)
        {
            var ranges = new List<CopyRange>();
            if (ArrayLocation(address) is { } element && types.Kind(element.Type.Element) == TypeKind.Struct
                && element.Offset + width / 8 <= types.Size(element.Type.Element))
            {
                if (!Recover(element.Array, null).TryGet(out var array, out var failure)) return failure;
                if (!Index(element.Index).TryGet(out var index, out failure)) return failure;
                var item = new ArrayElementValue(array, index, element.Type.Element, 0);
                ranges.Add(new(element.Type.Element, new AddressValue(item), element.Offset));
                foreach (var path in StructPaths(item.Type).Where(p => types.Kind(p.Type) == TypeKind.Struct
                    && p.Offset <= element.Offset && element.Offset + width / 8 <= p.Offset + types.Size(p.Type)))
                    ranges.Add(new(path.Type, new AddressValue(PathValue(item, path.Path)), element.Offset - path.Offset));
                return ranges.ToArray();
            }
            var (root, offset, rest) = Split(address);
            if (root is Symbol { Kind: SymbolKind.StaticFields, Value: DefinitionRef owner } && rest.Count == 0 && facts.Layouts.Of(owner) is { } layout)
            {
                // 静态字段中的结构体：静态数据没有对象头，偏移直接是字段偏移。
                foreach (var slot in layout.Statics.Where(s => types.Kind(s.Type) == TypeKind.Struct && s.Offset <= offset && offset + width / 8 <= s.Offset + types.Size(s.Type)))
                {
                    var field = new StaticFieldValue(new FieldRef(slot.Field, owner), slot.Type, 0);
                    ranges.Add(new(slot.Type, new AddressValue(field), (int)offset - slot.Offset));
                    foreach (var path in StructPaths(slot.Type).Where(p => types.Kind(p.Type) == TypeKind.Struct
                        && slot.Offset + p.Offset <= offset && offset + width / 8 <= slot.Offset + p.Offset + types.Size(p.Type)))
                        ranges.Add(new(path.Type, new AddressValue(PathValue(field, path.Path)), (int)offset - slot.Offset - path.Offset));
                }
                return ranges.ToArray();
            }
            if (root is null || rest.Count != 0 || TypeOfAddressBase(root) is not { } type) return ranges.ToArray();
            if (!Recover(root, null).TryGet(out var value, out _)) return ranges.ToArray();
            if (type is ByRefRef reference && types.Kind(reference.Element) == TypeKind.Struct && offset >= 0 && offset + width / 8 <= types.Size(reference.Element))
                ranges.Add(new(reference.Element, value, (int)offset));
            foreach (var path in StructPaths(type).Where(p => types.Kind(p.Type) == TypeKind.Struct
                && p.Offset <= offset && offset + width / 8 <= p.Offset + types.Size(p.Type)))
                ranges.Add(new(path.Type, new AddressValue(PathValue(value, path.Path)), (int)offset - path.Offset));
            return ranges.ToArray();
        }

        /// <summary>
        /// 结构体内的清零（例如 <c>this.&lt;&gt;u__1 = default</c> 编译成两个 64 位零写入，第二个覆盖 token 与其后的填充）：
        /// 写入范围落在同一个结构体值之内、只覆盖完整的叶子与填充时，逐叶子写零。填充不是托管值（ECMA-335 I.8.2.1），对照器也不比较它。
        /// </summary>
        [StoreRule(15)]
        private RecoveryResult<bool> StoreStructZero(Store store, List<ManagedStatement> output)
        {
            if (!FrameZero(store.Value) || FrameAccess(store.Target) is not null || store.Value.Width < 16) return false;
            var width = store.Value.Width;
            if (!CopyRanges(store.Target, width).TryGet(out var ranges, out var failure)) return failure;
            var range = ranges.OrderBy(r => types.Size(r.Type)).FirstOrDefault();
            if (range is null) return false;
            var leaves = StructPaths(range.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)
                && p.Offset < range.Offset + width / 8 && range.Offset < p.Offset + types.Size(p.Type)).ToArray();
            if (leaves.Length == 0 || leaves.Any(p => p.Offset < range.Offset || p.Offset + types.Size(p.Type) > range.Offset + width / 8)) return false;
            // 恰好是单个叶子的写入走普通路径。
            if (leaves is [var single] && single.Offset == range.Offset && types.Size(single.Type) * 8 == width) return false;
            // 清零恰好覆盖一个结构体位置（如状态机末尾的 <>u__1 = default）：整体 initobj，不逐叶子写私有字段。
            if (WholeStructAt(range, width) is { } whole)
            {
                output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
                return true;
            }
            foreach (var leaf in leaves)
            {
                var target = PathValue(range.Root, leaf.Path);
                output.Add(new ManagedStore(store.Address, target, types.Kind(leaf.Type) == TypeKind.Reference
                    ? new ConstantValue(0, leaf.Type, 64) : new ConstantValue(0, leaf.Type, target.Width)));
            }
            return true;
        }

        /// <summary>
        /// 写入覆盖整个结构体字段，且写入的是同类型结构体值的对应叶子（单叶子结构体，如 this._ctx = ct，CancellationToken 只有私有字段 _source）：
        /// 写成整体赋值，不逐叶子写私有字段。
        /// </summary>
        [StoreTargetRule(5)]
        private bool StoreWholeStruct(Store store, ManagedValue target, List<ManagedStatement> output)
        {
            // 写入目标：结构体字段本身，或结构体字段的唯一叶子；结构体大小等于写入宽度。由外向内是同大小的各层（如 <>u__1 与它的只读字段 task）。
            var candidates = new List<ManagedValue>();
            // 多叶子的写入目标（片）：各片都是同一个结构体位置的直接叶子时，从这个位置开始。
            ManagedValue? Outer(ManagedValue leaf) => leaf is FieldValue { Receiver: AddressValue { Target: var outer } } ? outer : null;
            var start = types.Kind(target.Type) == TypeKind.Struct ? target
                : target is Fragment pieces ? (pieces.Parts.Select(p => Outer(p.Value)).Distinct().ToArray() is [var common] ? common : null)
                : Outer(target);
            for (var layer = start;
                 layer is not null && types.Kind(layer.Type) == TypeKind.Struct && types.Size(layer.Type) * 8 == store.Value.Width;
                 layer = layer is FieldValue { Receiver: AddressValue { Target: var next } } ? next : null)
                candidates.Insert(0, layer);
            if (candidates.Count == 0) return false;
            var whole = candidates[0];
            // 写入零：default(T)（initobj），不写私有叶子（如状态机末尾的 <ct>5__2 = default）。
            if (FrameZero(store.Value))
            {
                output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(whole), whole.Type), new ComposedValue(whole.Type, [])));
                return true;
            }
            if (!Recover(store.Value, null).TryGet(out var source, out _)) return false;
            // 写入的值：同类型结构体值的叶子（单叶子），或各片都是同一个结构体值的叶子（寄存器传递的结构体参数/结果）。
            var parts = source is Fragment fragment ? fragment.Parts.Select(p => p.Value).ToArray() : [source];
            foreach (var layer in candidates)
            {
                var roots = parts.Select(p => StructRootOf(p, layer.Type)).Distinct().ToArray();
                if (roots is not [{ } value]) continue;
                output.Add(new ManagedStore(store.Address, new IndirectValue(new AddressValue(layer), layer.Type), value));
                return true;
            }
            return false;
        }

        /// <summary>
        /// 内联的 task.GetAwaiter()（UniTask&lt;T&gt;）：整体写入 awaiter 的只读字段 task 不是合法的 C#；写成 C# 编译器原本发出的
        /// awaiter = task.GetAwaiter()（标为内联，执行对照按 awaiter-census 建模：全部实例的结果都是 *this 的逐字节拷贝）。
        /// </summary>
        private ManagedBody RewriteAwaiters(ManagedBody body)
        {
            var changed = false;
            var blocks = body.Blocks.Select(block =>
            {
                var statements = new List<ManagedStatement>();
                foreach (var statement in block.Statements)
                {
                    if (statement is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: var layer } }, Value: var task } store
                        && AwaiterOf(store.Address, layer, task, statements))
                    {
                        changed = true;
                        continue;
                    }
                    statements.Add(statement);
                }
                return block with { Statements = statements };
            }).ToArray();
            return changed ? body with { Blocks = blocks } : body;
        }

        private bool AwaiterOf(ulong address, ManagedValue layer, ManagedValue task, List<ManagedStatement> output)
        {
            if (layer is not FieldValue { Field: { Field.Name: "task" } field, Receiver: AddressValue { Target: var awaiter } }
                || (field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) == 0
                || awaiter.Type is not DefinitionRef { Definition: { Name: "Awaiter", DeclaringType.FullName: "Cysharp.Threading.Tasks.UniTask" } }
                || task.Type is not DefinitionRef { Definition.FullName: "Cysharp.Threading.Tasks.UniTask", Arguments: [_] } unitask
                || unitask.Definition.Methods.FirstOrDefault(m => m is { Name: "GetAwaiter", IsStatic: false, Parameters.Count: 0, GenericParameters.Count: 0 }) is not { } getAwaiter)
                return false;
            ManagedValue? receiver = task switch
            {
                LocalValue or FieldValue or ArgumentValue => new AddressValue(task),
                IndirectValue indirect => indirect.Address,
                _ => null,
            };
            if (receiver is null) return false;
            var result = awaiter as LocalValue ?? StructLocal(awaiter.Type, 0);
            output.Add(new ManagedCall(address, new ManagedInvocation(new MethodRef(getAwaiter, unitask.Arguments, []), receiver, [], false), result, false) { Inlined = true });
            if (!ReferenceEquals(result, awaiter)) output.Add(new ManagedStore(address, new IndirectValue(new AddressValue(awaiter), awaiter.Type), result));
            return true;
        }

        /// <summary>范围内恰好从 range.Offset 开始、大小为 width 的最外层结构体位置。</summary>
        private ManagedValue? WholeStructAt(CopyRange range, int width)
        {
            if (types.Kind(range.Type) == TypeKind.Struct && range.Offset == 0 && types.Size(range.Type) * 8 == width)
                return range.Root is AddressValue address ? address.Target : new IndirectValue(range.Root, range.Type);
            var path = StructPaths(range.Type).Where(p => p.Offset == range.Offset && types.Kind(p.Type) == TypeKind.Struct && types.Size(p.Type) * 8 == width)
                .OrderBy(p => p.Path.Length).FirstOrDefault();
            return path.Path is null ? null : PathValue(range.Root, path.Path);
        }

        /// <summary>叶子值的结构体根（逐层剥去字段与取址，直到类型为 type）。</summary>
        private static ManagedValue? StructRootOf(ManagedValue leaf, TypeRef type)
        {
            for (var value = leaf; value is not null; )
            {
                if (value.Type.Equals(type)) return value;
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
        private RecoveryFailure? FrameCopies()
        {
            if (!PrepareFrameCopies().TryGet(out _, out var failure)) return failure;
            if (PrepareStructZeroes() is { } zeroFailure) return zeroFailure;
            PrepareFrameZeroes();
            PrepareStoredResults();
            return null;
        }

        /// <summary>
        /// 同一块内相邻的零写入合起来覆盖一个结构体帧区域的全部叶子（IL2CPP 的局部变量清零，如 AnimatorStateInfo）时，写成整体 initobj：
        /// 逐叶子写零会写到私有字段，initobj 与原生的整段清零（含填充）相同。跨区域的写入不合并。
        /// </summary>
        private void PrepareFrameZeroes()
        {
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var run = new List<(Store Store, FrameRegion Region, long Offset)>();
                    for (var j = i; j < block.Statements.Count && block.Statements[j] is Store s && !frameCopies.ContainsKey(s) && FrameZero(s.Value)
                        && FrameAccess(s.Target) is { } access; j++)
                        run.Add((s, access.Region, access.Offset));
                    if (run.Count == 0) continue;
                    foreach (var group in run.GroupBy(r => r.Region))
                    {
                        var region = group.Key;
                        if (types.Kind(region.Type) != TypeKind.Struct || group.Any(r => r.Offset < 0 || r.Offset + r.Store.Value.Width / 8 > region.Size)) continue;
                        var covered = group.SelectMany(r => Enumerable.Range((int)r.Offset, r.Store.Value.Width / 8)).ToHashSet();
                        if (StructPaths(region.Type).Any(p => types.Kind(p.Type) is not (TypeKind.Struct or null) && Enumerable.Range(p.Offset, types.Size(p.Type)).Any(b => !covered.Contains(b))))
                            continue;
                        var first = group.First().Store;
                        frameCopies[first] = [new ManagedStore(first.Address, new IndirectValue(new AddressValue(region.Local), region.Type), new ComposedValue(region.Type, []))];
                        foreach (var other in group.Skip(1)) frameCopies[other.Store] = [];
                    }
                    i += run.Count - 1;
                }
        }

        /// <summary>
        /// 同一块内相邻的零写入合起来覆盖一个结构体值的全部叶子（如 <c>this.&lt;&gt;u__1 = default</c> 的两个 64 位写入）时，写成整体 initobj：
        /// 逐叶子写零会写到只读字段（UniTask.source），而 initobj 与原生的整段清零（含填充）相同。
        /// </summary>
        private RecoveryFailure? PrepareStructZeroes()
        {
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (frameCopies.ContainsKey(block.Statements[i]) || block.Statements[i] is not Store first || !FrameZero(first.Value) || FrameAccess(first.Target) is not null) continue;
                    var run = new List<Store>();
                    for (var j = i; j < block.Statements.Count && block.Statements[j] is Store s && FrameZero(s.Value) && FrameAccess(s.Target) is null && !frameCopies.ContainsKey(s); j++) run.Add(s);
                    if (run.Count < 2) continue;
                    var ranges = new List<CopyRange[]>();
                    foreach (var store in run)
                    {
                        if (!CopyRanges(store.Target, store.Value.Width).TryGet(out var candidates, out var failure)) return failure;
                        ranges.Add(candidates);
                    }
                    // 候选是第一条写入所在的结构体值（从外到内）；每条写入都须落在其中，并合起来覆盖它的全部叶子。
                    foreach (var whole in ranges[0].Where(r => r.Offset == 0).OrderByDescending(r => types.Size(r.Type)))
                    {
                        var size = types.Size(whole.Type);
                        var covered = new HashSet<int>();
                        var count = 0;
                        foreach (var (store, candidates) in run.Zip(ranges))
                        {
                            if (candidates.FirstOrDefault(r => r.Type.Equals(whole.Type) && r.Root.Equals(whole.Root)) is not { } inner || inner.Offset + store.Value.Width / 8 > size) break;
                            for (var k = 0; k < store.Value.Width / 8; k++) covered.Add(inner.Offset + k);
                            count++;
                        }
                        if (count < 2 || StructPaths(whole.Type).Any(p => types.Kind(p.Type) is not (TypeKind.Struct or null)
                            && Enumerable.Range(p.Offset, types.Size(p.Type)).Any(b => !covered.Contains(b)))) continue;
                        frameCopies[run[0]] = [new ManagedStore(run[0].Address, new IndirectValue(whole.Root, whole.Type), new ComposedValue(whole.Type, []))];
                        foreach (var store in run.Skip(1).Take(count - 1)) frameCopies[store] = [];
                        i += count - 1;
                        break;
                    }
                }
            return null;
        }

        /// <summary>
        /// 寄存器返回的结构体按片写进同类型的帧区域（帧见证 <c>WitnessStoredResults</c>），同一块内相邻写入覆盖全部片时，写成一次整体赋值：
        /// 逐叶子写入只读字段（UniTask.source）不是合法 IL，整体赋值与原生逐片写入的结果相同。
        /// </summary>
        private void PrepareStoredResults()
        {
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    if (block.Statements[i] is not Store { Value: Use first } store || frameCopies.ContainsKey(store) || FrameAccess(store.Target) is not { } access
                        || !results.TryGetValue(first.Variable, out var result) || Resolve(result.Call) is not { } callee
                        || owner.abi.Classify(callee, out _)?.Return is not { } returned || !RegisterStruct(returned) || !access.Region.Type.Equals(returned.Type)) continue;
                    var pieces = new List<Store>();
                    for (var j = i; j < block.Statements.Count && pieces.Count < returned.Pieces.Length; j++)
                    {
                        if (block.Statements[j] is not Store { Value: Use piece } next || FrameAccess(next.Target) is not { } at || at.Region != access.Region
                            || !results.TryGetValue(piece.Variable, out var r) || !ReferenceEquals(r.Call, result.Call)) break;
                        var abi = returned.Pieces.FirstOrDefault(p => p.Register == result.Call.Results[r.Index]);
                        if (abi is null || abi.Offset != at.Offset || abi.Width != next.Value.Width) break;
                        pieces.Add(next);
                    }
                    if (pieces.Count != returned.Pieces.Length || pieces.Select(p => FrameAccess(p.Target)!.Value.Offset).Distinct().Count() != pieces.Count) continue;
                    frameCopies[pieces[0]] = [new ManagedStore(pieces[0].Address, new IndirectValue(new AddressValue(access.Region.Local), access.Region.Type), CallStructLocal(result.Call, returned.Type))];
                    foreach (var piece in pieces.Skip(1)) frameCopies[piece] = [];
                    i += pieces.Count - 1;
                }
        }

        /// <summary>帧区域之间的整体拷贝替代原来的逐字访存。</summary>
        [StatementRule(10)]
        private bool LowerFrameCopy(Block block, Stmt statement, List<ManagedStatement> output)
        {
            if (!frameCopies.TryGetValue(statement, out var copy)) return false;
            output.AddRange(copy);
            return true;
        }

        /// <summary>拷贝中的一段读取：整体读取，或窄读取零扩展到寄存器（写入时再取回原宽度，如 20 字节结构体的末 4 字节）。</summary>
        private static Load? CopiedLoad(Expr value) => value switch
        {
            Load load => load,
            Ir.Convert { Kind: ConvKind.ZeroExtend, Operand: Load { Width: 32 or 16 or 8 } inner } => inner,
            _ => null,
        };

        private RecoveryResult<bool> PrepareFrameCopies()
        {
            var statements = blocks.SelectMany(b => b.Statements).ToArray();
            var uses = new Dictionary<Variable, List<Stmt>>();
            foreach (var statement in statements)
            {
                // 间接返回由 x8 指向的完整缓冲区决定，L2 的返回寄存器不参与托管返回值。
                if (statement is Return && ownReturnBuffer is not null) continue;
                var variables = statement is Phi phi ? phi.Sources : ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
                foreach (var variable in variables)
                {
                    if (!uses.TryGetValue(variable, out var list)) uses[variable] = list = [];
                    list.Add(statement);
                }
            }
            var copies = new List<FrameCopy>();
            foreach (var define in statements.OfType<Define>())
            {
                if (CopiedLoad(define.Value) is not { Width: 64 or 128 or 32 } load || !uses.TryGetValue(define.Target, out var users)
                    || users is not [Store { Value: Use use } store] || use.Width != load.Width || dropped.Contains(store)) continue;
                // 至少一端是栈结构体根时可以逐叶子拷贝；两端都不在栈上时，只接受下面合并成的整体拷贝（覆盖整个结构体）。
                var onFrame = FrameAccess(load.Address) is not null || FrameAccess(store.Target) is not null;
                if (!CopyRanges(load.Address, load.Width).TryGet(out var sources, out var failure)) return failure;
                if (!CopyRanges(store.Target, load.Width).TryGet(out var targets, out failure)) return failure;
                var pairs = (from source in sources
                             from target in targets
                             where source.Type.Equals(target.Type) && source.Offset == target.Offset
                             orderby types.Size(source.Type)
                             select (source, target)).ToArray();
                if (pairs.Length == 0) continue;
                var smallest = pairs.Where(p => types.Size(p.source.Type) == types.Size(pairs[0].source.Type)).Distinct().ToArray();
                // 同样大小、在同一偏移互相嵌套的结构体（例如 UniTask.Awaiter 只有一个 UniTask 字段）覆盖相同的叶子，取最外层，逐叶子拷贝的结果相同。
                if (smallest.Length > 1)
                    smallest = smallest.Where(p => smallest.All(q => q == p || StructPaths(p.source.Type).Any(path => path.Offset == 0 && path.Type.Equals(q.source.Type)))).ToArray();
                if (smallest.Length != 1) continue;
                var (from, to) = smallest[0];
                if (from.Type is GenericParameterRef { NativeAggregate: not null })
                {
                    // 开放 T 没有可访问的实例字段；只允许后续完整覆盖检查把所有片合并成一次复制。
                    copies.Add(new FrameCopy(define, store, from, to, new Fragment([], types.UInt64, load.Width)));
                    continue;
                }
                var paths = StructPaths(from.Type).Where(p => types.Kind(p.Type) is not (TypeKind.Struct or null)).OrderBy(p => p.Offset).ToArray();
                var touched = paths.Where(p => p.Offset < from.Offset + load.Width / 8 && from.Offset < p.Offset + types.Size(p.Type)).ToArray();
                if (touched.Length == 0 || touched.Any(p => p.Offset < from.Offset || p.Offset + types.Size(p.Type) > from.Offset + load.Width / 8)) continue;
                if (touched.Zip(touched.Skip(1)).Any(p => p.First.Offset + types.Size(p.First.Type) > p.Second.Offset)) continue;
                var snapshot = new Fragment(touched.Select(p => new Part((p.Offset - from.Offset) * 8,
                    StructLocal(p.Type, types.Size(p.Type) * 8))).ToArray(), types.UInt64, load.Width);
                var copy = new FrameCopy(define, store, from, to, snapshot);
                copies.Add(copy);
                if (!onFrame) continue;
                frameCopies[define] = touched.Select((p, i) => (ManagedStatement)new ManagedAssignment(define.Address,
                    (LocalValue)snapshot.Parts[i].Value, PathValue(from.Root, p.Path))).ToArray();
                frameCopies[store] = touched.Select((p, i) => (ManagedStatement)new ManagedStore(store.Address,
                    PathValue(to.Root, p.Path), snapshot.Parts[i].Value)).ToArray();
            }
            // 完整复制仅在“先读完、后写入”的连续序列中合并，跨调用/未知访存不得移动快照。
            foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var first = copies.FirstOrDefault(c => ReferenceEquals(c.Load, block.Statements[i]));
                if (first is null) continue;
                var sequence = new List<FrameCopy>();
                var start = i;
                while (i < block.Statements.Count && copies.FirstOrDefault(c => ReferenceEquals(c.Load, block.Statements[i])) is { } next
                    && next.Source.Type.Equals(first.Source.Type) && next.Source.Root.Equals(first.Source.Root) && next.Target.Root.Equals(first.Target.Root))
                { sequence.Add(next); i++; }
                var stores = block.Statements.Skip(i).Take(sequence.Count).ToArray();
                if (stores.Length != sequence.Count || !sequence.All(c => stores.Any(s => ReferenceEquals(s, c.Store)))) { i = start; continue; }
                var intervals = sequence.OrderBy(c => c.Source.Offset).ToArray();
                var cursor = 0;
                foreach (var copy in intervals)
                {
                    if (copy.Source.Offset != cursor) { cursor = -1; break; }
                    cursor += copy.Snapshot.Width / 8;
                }
                if (cursor != types.Size(first.Source.Type)) { i = start; continue; }
                var value = StructLocal(first.Source.Type, 0);
                foreach (var copy in sequence) { frameCopies[copy.Load] = []; frameCopies[copy.Store] = []; }
                frameCopies[first.Load] = [new ManagedAssignment(first.Load.Address, value, new IndirectValue(first.Source.Root, first.Source.Type))];
                var last = (Store)stores[^1];
                frameCopies[last] = [new ManagedStore(last.Address, new IndirectValue(first.Target.Root, first.Target.Type), value)];
                i += stores.Length - 1;
            }
            return copies.Count != 0;
        }
    }
}
