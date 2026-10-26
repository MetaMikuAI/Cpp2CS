using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private sealed record StackEnum(DefinitionRef Type, Expr Value, long Offset, Store[] Stores);
        private readonly Dictionary<Call, StackEnum> stackEnums = new(ReferenceEqualityComparer.Instance);
        private readonly HashSet<Stmt> stackEnumStorage = new(ReferenceEqualityComparer.Instance);

        /// <summary>Il2CppFakeBox 的类指针、栈标记和枚举值组成临时装箱；仅接收不逃逸的 Enum 实例调用。</summary>
        [Analysis("栈上枚举", 28, After = ["异常值", "栈上调用"])]
        private void PrepareStackEnums()
        {
            var candidates = new Dictionary<Call, StackEnum>(ReferenceEqualityComparer.Instance);
            BranchStackEnums(candidates);
            foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Store { Target: FrameAddress }) continue;
                var stores = new List<Store>();
                foreach (var statement in Straight(block, i - 1))
                {
                    if (statement is Define or Nop) continue;
                    if (statement is Store { Target: FrameAddress } store && stores.Count < 3) { stores.Add(store); continue; }
                    if (statement is Call call && stores.Count == 3 && stores.Select(s => ((FrameAddress)s.Target).Offset).Distinct().Count() == 3
                        && Receiver(call) is { } receiver && FrameOffset(receiver) is { } offset
                        && Resolve(call) is { Method: { IsStatic: false, Owner.FullName: "System.Enum" } } callee
                        && call.Arguments.Skip(1).All(a => !ExprMap.Walk(a).Any(p => FrameOffset(p) is not null)))
                    {
                        var klass = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectKlass);
                        var monitor = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectMonitor);
                        var data = stores.SingleOrDefault(s => ((FrameAddress)s.Target).Offset == offset + RuntimeLayout.ObjectHeaderSize);
                        if (klass?.Value is Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }
                            && monitor?.Value is Const { Width: 64, Value: ulong.MaxValue } && data is not null
                            && data.Value.Width == types.Bits(type))
                        {
                            candidates[call] = new(type, data.Value, offset, stores.ToArray());
                            resolved[call] = (callee, Pinned);
                        }
                    }
                    break;
                }
            }
            foreach (var group in candidates.GroupBy(p => p.Value.Offset))
            {
                var members = group.ToArray();
                var end = group.Key + RuntimeLayout.ObjectHeaderSize + members.Max(p => types.Size(p.Value.Type));
                var covered = members.SelectMany(p => p.Value.Stores.Cast<Stmt>().Append(p.Key)).ToHashSet(ReferenceEqualityComparer.Instance);
                // 地址逃逸不能按物理栈槽重绑定；其他生命期的读写由覆盖前读取检查区分。
                if (blocks.SelectMany(b => b.Statements).Any(s => !covered.Contains(s)
                    && (s is Define d && FrameOffset(d.Value) is { } value && value >= group.Key && value < end
                        || s is Store stored && FrameOffset(stored.Value) is { } pointer && pointer >= group.Key && pointer < end))) continue;
                foreach (var (call, box) in members)
                {
                    if (StackBoxReadAfter(call, box)) continue;
                    stackEnums[call] = box;
                    dropped.UnionWith(box.Stores);
                    stackEnumStorage.UnionWith(box.Stores);
                    stackEnumStorage.Add(call);
                }
            }
        }

        private void BranchStackEnums(Dictionary<Call, StackEnum> candidates)
        {
            var next = blocks.SelectMany(b => b.Statements).SelectMany(s => s switch
            {
                Define d => new[] { d.Target }, Phi p => p.Sources.Append(p.Target), Call c => c.Defines.OfType<Variable>(), _ => [],
            }).Where(v => v.Storage.Bank == Bank.Temp).Select(v => v.Storage.Index).DefaultIfEmpty(-1).Max() + 1;
            foreach (var block in blocks)
            foreach (var call in block.Statements.OfType<Call>().ToArray())
            {
                if (Receiver(call) is not { } receiver || FrameOffset(receiver) is not { } offset
                    || Resolve(call) is not { Method: { IsStatic: false, Owner.FullName: "System.Enum" } } callee) continue;
                var prefix = block.Statements.TakeWhile(s => !ReferenceEquals(s, call)).Where(s => s is not (Phi or Define or Nop)).ToArray();
                if (prefix is not [Store klass, Store monitor]
                    || FrameOffset(klass.Target) != offset || FrameOffset(monitor.Target) != offset + RuntimeLayout.ObjectMonitor
                    || klass.Value is not Symbol { Kind: SymbolKind.Class, Value: DefinitionRef { Definition.IsEnum: true } type }
                    || monitor.Value is not Const { Width: 64, Value: ulong.MaxValue } || block.Predecessors.Count < 2) continue;
                var writes = new List<Store>();
                foreach (var parent in block.Predecessors)
                {
                    var store = parent.Statements.OfType<Store>().LastOrDefault(s => FrameOffset(s.Target) == offset + RuntimeLayout.ObjectHeaderSize);
                    if (store is null || store.Value.Width != types.Bits(type) || parent.NormalSuccessors.ToArray() is not [var target] || target != block
                        || parent.Statements.Skip(parent.Statements.IndexOf(store) + 1).Any(s => s is not (Define or Jump or Nop))) break;
                    writes.Add(store);
                }
                if (writes.Count != block.Predecessors.Count) continue;
                var inputs = writes.Select(_ => new Variable(Storage.Temp(next++), 1)).ToArray();
                for (var i = 0; i < writes.Count; i++)
                    InsertAnalysisStatement(block.Predecessors[i], block.Predecessors[i].Statements.IndexOf(writes[i]), new Define(writes[i].Address, inputs[i], writes[i].Value));
                var result = new Variable(Storage.Temp(next++), 1);
                InsertAnalysisStatement(block, 0, new Phi(block.Start, result, inputs));
                candidates[call] = new(type, new Use(result, types.Bits(type)), offset, [klass, monitor, .. writes]);
                resolved[call] = (callee, Pinned);
            }
            if (candidates.Count > 0) definitions = IndexDefinitions();
        }

        // Enum 调用后，盒内字节在被覆盖之前不能再被原生代码读取。
        private bool StackBoxReadAfter(Call call, StackEnum box)
        {
            var size = RuntimeLayout.ObjectHeaderSize + types.Size(box.Type);
            uint Bytes(long offset, int count)
            {
                var first = (int)Math.Clamp(offset - box.Offset, 0, size);
                var end = (int)Math.Clamp(offset - box.Offset + count, 0, size);
                return ((1u << (end - first)) - 1) << first;
            }
            bool Reads(Expr value, uint live) => ExprMap.Walk(value).Any(e =>
                e is Load load && FrameOffset(load.Address) is { } offset && (Bytes(offset, load.Width / 8) & live) != 0
                || FrameOffset(e) is { } address && (Bytes(address, 1) & live) != 0);
            var firstBlock = blocks.Single(b => b.Statements.Contains(call));
            var pending = new Queue<(Block Block, int Position, uint Live)>();
            pending.Enqueue((firstBlock, firstBlock.Statements.IndexOf(call) + 1, (1u << size) - 1));
            var seen = new Dictionary<(Block, int), uint>();
            while (pending.TryDequeue(out var item))
            {
                var key = (item.Block, item.Position);
                var previous = seen.GetValueOrDefault(key);
                if ((item.Live & ~previous) == 0) continue;
                seen[key] = previous | item.Live;
                var live = item.Live;
                if (item.Block.Handler is { } handler) pending.Enqueue((handler, 0, live));
                foreach (var statement in item.Block.Statements.Skip(item.Position))
                {
                    if (statement is Call barrier && IsWriteBarrier(barrier)) continue;
                    if (statement is Store store && FrameOffset(store.Target) is { } target)
                    {
                        if (Reads(store.Value, live)) return true;
                        live &= ~Bytes(target, store.Value.Width / 8);
                    }
                    else if (statement is Call next && Resolve(next) is { } callee
                        && owner.abi.Classify(callee, out _)?.Return is { Passing: Passing.Indirect, Pieces: [var piece] } result
                        && ArgumentsOf(next).TryGetValue(piece.Register, out var buffer) && FrameOffset(buffer) is { } destination)
                    {
                        if (Reads(next.Target, live) || next.Arguments.Where((_, i) => i >= next.Sources.Length || next.Sources[i] != piece.Register).Any(a => Reads(a, live))) return true;
                        live &= ~Bytes(destination, types.Size(result.Type));
                    }
                    else if (ExprMap.Operands(statement).Any(e => Reads(e, live))) return true;
                    if (live == 0) break;
                }
                if (live != 0)
                    foreach (var successor in item.Block.NormalSuccessors) pending.Enqueue((successor, 0, live));
            }
            return false;
        }
    }
}
