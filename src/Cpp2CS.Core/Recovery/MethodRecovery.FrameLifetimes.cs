using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>
        /// x8 全定义切断前值的存活期。只拆唯一前驱/后继直线链，同一时期全部类型见证必须相容；
        /// 帧地址若保存在 SSA 变量或写进内存，可能跨过覆盖点，不能按最近物理偏移重绑定。
        /// 分支合流、非整值定义和不相容的中途使用继续留“栈槽类型冲突”。
        /// </summary>
        private void PrepareColoredFrames(FrameRegion[] candidates, List<FrameWitness> witnesses)
        {
            var chains = new List<Stmt[]>();
            var visited = new HashSet<Block>();
            foreach (var first in blocks)
            {
                if (visited.Contains(first)) continue;
                var chain = new List<Stmt>();
                var block = first;
                while (visited.Add(block))
                {
                    chain.AddRange(block.Statements);
                    var next = block.NormalSuccessors.ToArray();
                    if (next is not [var only] || only.Predecessors.Count != 1) break;
                    block = only;
                }
                chains.Add(chain.ToArray());
            }
            foreach (var offset in conflictingFrames.ToArray())
            {
                var definitions = witnesses.Where(w => w.Offset == offset && w.Writes).ToArray();
                if (definitions.Select(w => w.Type).Distinct().Count() < 2) continue;
                var size = definitions.Max(w => types.Size(w.Type));
                var related = witnesses.Where(w => w.Offset >= offset && w.Offset < offset + size).ToArray();
                // 非嵌套的其他起点重叠会要求更一般的区间别名分析。
                if (candidates.Any(r => r.Offset < offset && offset < r.Offset + r.Size)) continue;
                var users = blocks.SelectMany(b => b.Statements).Where(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk)
                    .OfType<FrameAddress>().Any(f => f.Offset >= offset && f.Offset < offset + size)).ToArray();
                if (users.Any(s => s is Define d && FrameOffset(d.Value) is not null
                    || s is Store store && FrameOffset(store.Value) is not null)) continue;
                var chain = chains.SingleOrDefault(c => related.All(w => c.Contains(w.Call)) && users.All(c.Contains));
                if (chain is null) continue;
                var ordered = definitions.OrderBy(w => Array.IndexOf(chain, w.Call)).ToArray();
                var split = new List<(FrameRegion Region, HashSet<Stmt> Live)>();
                var valid = true;
                for (var i = 0; i < ordered.Length; i++)
                {
                    var definition = ordered[i];
                    var start = Array.IndexOf(chain, definition.Call);
                    var end = i + 1 == ordered.Length ? chain.Length : Array.IndexOf(chain, ordered[i + 1].Call);
                    var live = chain[start..end].ToHashSet();
                    var region = new FrameRegion(offset, definition.Type, types.Size(definition.Type), StructLocal(definition.Type, ScalarWidth(definition.Type)));
                    if (related.Any(w => live.Contains(w.Call) && !ContainsFrameType(region, w.Offset, w.Type))) { valid = false; break; }
                    split.Add((region, live));
                }
                if (!valid) continue;
                frameRegions.RemoveAll(r => r.Offset >= offset && r.Offset + r.Size <= offset + size);
                foreach (var (region, live) in split) { frameRegions.Add(region); frameLives[region] = live; }
                // 成功替换的使用已没有 FrameAddress；未覆盖的更早使用仍须报告类型冲突。
            }
            foreach (var offset in conflictingFrames.ToArray())
                if (!frameLives.Keys.Any(r => r.Offset == offset)) ReachingFrames(offset, candidates, witnesses);
        }

        /// <summary>
        /// 一般控制流上的栈槽复用（C++ 编译器让生命期不相交的局部变量共用栈槽）：完整定义栈槽的见证（x8 间接返回、值类型构造函数的 this、
        /// 寄存器结构体结果写入、拷贝写入）切断前一个生命期。每个使用取到达它的定义（前向数据流，定义互相覆盖）；
        /// 没有到达定义的使用（如构造前的清零）取它之后各路径上最先遇到的定义。到达的定义类型唯一时归入该类型的区域，否则保留冲突。
        /// 帧地址保存在 SSA 变量或写进内存时可能跨过覆盖点，不拆。
        /// </summary>
        private void ReachingFrames(long offset, FrameRegion[] candidates, List<FrameWitness> witnesses)
        {
            var at = witnesses.Where(w => w.Offset == offset).ToArray();
            if (at.Select(w => w.Type).Distinct().Count() < 2) return;
            var size = at.Max(w => types.Size(w.Type));
            if (candidates.Any(r => r.Offset < offset && offset < r.Offset + r.Size || r.Offset < offset + size && offset + size < r.Offset + r.Size)) return;
            // 与已经拆分过生命期的区域重叠时不再拆（两种拆分会让同一语句落在两个区域）。
            if (frameLives.Keys.Any(r => r.Offset < offset + size && offset < r.Offset + r.Size)) return;
            var related = witnesses.Where(w => w.Offset >= offset && w.Offset < offset + size).ToArray();
            bool Touches(Stmt s) => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<FrameAddress>().Any(f => f.Offset >= offset && f.Offset < offset + size);
            var users = blocks.SelectMany(b => b.Statements).Where(Touches).ToHashSet();
            if (users.Any(s => s is Define d && FrameOffset(d.Value) is not null || s is Store store && FrameOffset(store.Value) is not null)) return;
            // 定义：写满整个槽（从槽起点开始、大小等于该类型）的见证。
            bool Defines(FrameWitness w) => w.Writes || w.Call is Store
                || w.Call is Call call && (!call.Arguments.Any(a => FrameOffset(a) == offset)
                    || Resolve(call) is { Method: { Name: ".ctor", IsStatic: false, Owner.IsValueType: true } } constructor && ArgumentsOf(call).Values.FirstOrDefault() is { } self
                        && FrameOffset(self) == offset && constructor.DeclaringType.Equals(w.Type));
            var definitions = at.Where(Defines).ToArray();
            if (definitions.Select(w => w.Type).Distinct().Count() < 2) return;
            var defining = new Dictionary<Stmt, TypeRef[]>(ReferenceEqualityComparer.Instance);
            foreach (var definition in definitions)
                defining[definition.Call] = defining.TryGetValue(definition.Call, out var known) ? known.Append(definition.Type).Distinct().ToArray() : [definition.Type];
            if (defining.Values.Any(t => t.Length != 1)) return;
            // 前向：到达每条语句入口的定义类型集合（null = 尚无定义）。
            var input = new Dictionary<Block, HashSet<TypeRef?>>();
            var output = new Dictionary<Block, HashSet<TypeRef?>>();
            HashSet<TypeRef?> Transfer(Block block, HashSet<TypeRef?> state, Dictionary<Stmt, HashSet<TypeRef?>>? record)
            {
                var current = new HashSet<TypeRef?>(state);
                foreach (var statement in block.Statements)
                {
                    record?.Add(statement, new(current));
                    if (defining.TryGetValue(statement, out var type)) current = [type[0]];
                }
                return current;
            }
            var entryBlock = blocks[0];
            foreach (var block in blocks) output[block] = [];
            bool changed;
            do
            {
                changed = false;
                foreach (var block in blocks)
                {
                    var state = new HashSet<TypeRef?>();
                    if (block == entryBlock || block.Predecessors.Count == 0) state.Add(null);
                    foreach (var predecessor in block.Predecessors) if (output.TryGetValue(predecessor, out var before)) state.UnionWith(before);
                    input[block] = state;
                    var result = Transfer(block, state, null);
                    if (!result.SetEquals(output[block])) { output[block] = result; changed = true; }
                }
            } while (changed);
            var reaching = new Dictionary<Stmt, HashSet<TypeRef?>>(ReferenceEqualityComparer.Instance);
            foreach (var block in blocks) Transfer(block, input[block], reaching);
            // 后向：每条语句之后各路径上最先遇到的定义类型（用于没有到达定义的使用）。
            var ahead = new Dictionary<Block, HashSet<TypeRef>>();
            foreach (var block in blocks) ahead[block] = [];
            HashSet<TypeRef> Ahead(Block block, int from)
            {
                for (var i = from; i < block.Statements.Count; i++)
                    if (defining.TryGetValue(block.Statements[i], out var type)) return [type[0]];
                var result = new HashSet<TypeRef>();
                foreach (var successor in block.Successors) if (ahead.TryGetValue(successor, out var after)) result.UnionWith(after);
                return result;
            }
            do
            {
                changed = false;
                foreach (var block in blocks)
                {
                    var result = Ahead(block, 0);
                    if (!result.SetEquals(ahead[block])) { ahead[block] = result; changed = true; }
                }
            } while (changed);
            var lives = new Dictionary<TypeRef, HashSet<Stmt>>();
            TypeRef? FollowingDefinition(Block block, int position)
            {
                var seen = new HashSet<Block>();
                while (seen.Add(block))
                {
                    foreach (var statement in block.Statements.Skip(position))
                    {
                        if (defining.TryGetValue(statement, out var own)) return own[0];
                        if (Touches(statement)) return null;
                    }
                    if (block.NormalSuccessors.ToArray() is not [var next] || next.Predecessors.Count != 1) return null;
                    block = next;
                    position = 0;
                }
                return null;
            }
            foreach (var block in blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var statement = block.Statements[i];
                    if (!users.Contains(statement)) continue;
                    TypeRef? type;
                    // 构造前的整值清零属于新生命期；不同分支遗留的旧类型不参与这次写入。
                    if (statement is Store clear && FrameOffset(clear.Target) == offset && FrameZero(clear.Value)
                        && FollowingDefinition(block, i + 1) is { } nextType && clear.Value.Width == types.Size(nextType) * 8) type = nextType;
                    else if (defining.TryGetValue(statement, out var own)) type = own[0];
                    else
                    {
                        var reached = reaching[statement];
                        if (reached.Contains(null))
                        {
                            if (reached.Count > 1) return;
                            var next = Ahead(block, i + 1);
                            if (next.Count != 1) return;
                            type = next.Single();
                        }
                        else if (reached.Count == 1) type = reached.Single();
                        else return;
                    }
                    if (!lives.TryGetValue(type!, out var live)) lives[type!] = live = new(ReferenceEqualityComparer.Instance);
                    live.Add(statement);
                }
            var split = lives.Select(p => (Region: new FrameRegion(offset, p.Key, types.Size(p.Key), StructLocal(p.Key, ScalarWidth(p.Key))), Live: p.Value)).ToArray();
            // 每个生命期内的全部类型见证都须与区域相容。
            foreach (var (region, live) in split)
                if (related.Any(w => live.Contains(w.Call) && !ContainsFrameType(region, w.Offset, w.Type))) return;
            frameRegions.RemoveAll(r => r.Offset >= offset && r.Offset + r.Size <= offset + size);
            foreach (var (region, live) in split) { frameRegions.Add(region); frameLives[region] = live; }
        }
    }
}
