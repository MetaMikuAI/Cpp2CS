using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery.Runtime;

namespace Cpp2CS.Idioms;

/// <summary>
/// 幂等初始化守卫：if (!flag) init(); 之后 clang 可把后续计算复制到两臂，并让快路径复用守卫之前读到的值。
/// 快路径上初始化已经完成，在其开头补上 init 也不改变行为，所以两臂的差别只在写法：
/// 把两臂的写入、合流值或出口分支归一到“守卫处的内存内容”后逐项比较，相同时只保留初始化一臂。
/// 类构造、类布局与方法元数据的守卫共用这一证明；证明不成立时保留原分支并记录原因。
/// </summary>
internal static class OnceGuardsPass
{
    private enum Kind { Metadata, ClassConstructor, ClassLayout }
    private sealed record Guard(Kind Kind, Block Initialize, Block Skip, TypeRef? Type, ulong Flag);

    /// <summary>折叠一个守卫；调用方在清理后继续寻找下一个。</summary>
    internal static bool OnceGuards(this IdiomState state)
    {
        foreach (var head in state.function.Blocks)
        {
            if (state.removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch || Recognize(state, head, branch) is not { } guard) continue;
            var proof = new Proof(state, head, guard);
            if (!proof.Holds(out var reason))
            {
                state.Reject($"once.{guard.Kind}", branch.Address, reason);
                continue;
            }
            if (guard.Kind == Kind.Metadata) proof.CommitMetadata(branch);
            head.Statements[^1] = new Jump(branch.Address, guard.Initialize.Start);
            MachineFunction.RemoveEdge(head, guard.Skip);
            return true;
        }
        return false;
    }

    private static Guard? Recognize(IdiomState state, Block head, Branch branch)
    {
        if (head.NormalSuccessors.ToArray() is not [var first, var second]) return null;
        var condition = state.defs.Expand(branch.Condition);
        if (TopLoadsPass.TopLoads(condition).Distinct().ToArray() is not [var flag]) return null;
        var side = DirectionPass.Direction(condition, ReplacePass.Replace(flag, 0));
        if (side is not (0 or 1) || DirectionPass.Direction(condition, ReplacePass.Replace(flag, 1)) != 1 - side) return null;
        var (initialize, skip) = side == 0 ? (first, second) : (second, first);
        switch (flag)
        {
            case { Width: 8, Address: Const address } when state.owner.guardSections.Any(s => s.Contains(address.Value)):
                return new(Kind.Metadata, initialize, skip, null, address.Value);
            case { Width: 32, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type }, Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor } } }:
                // 类自身的静态构造中，标志位的含义不同。
                return state.self?.Method.Name == ".cctor" ? null : new(Kind.ClassConstructor, initialize, skip, type, 0);
            case { Width: 8 or 16, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type }, Right: Const { Value: RuntimeLayout.ClassBitflags1 } } }
                when ClassInitializationFlags.IsBitTest(condition, flag):
                return new(Kind.ClassLayout, initialize, skip, type, 0);
            default:
                return null;
        }
    }

    /// <summary>一臂的走法：环境、写入与终点。</summary>
    private sealed class Line
    {
        public Dictionary<Variable, Expr> Values { get; } = [];
        /// <summary>守卫之前的定义归一后的结果。</summary>
        public Dictionary<Variable, Expr> Expanded { get; } = [];
        public List<(Expr Target, Expr Value)> Stores { get; } = [];
        public Block Previous { get; set; } = null!;
        public Block? Merge { get; set; }
        public Branch? Exit { get; set; }
        public bool Initialized { get; set; }
        public List<ulong> Slots { get; } = [];
        public Store? FlagStore { get; set; }
        public Block? FlagBlock { get; set; }
    }

    private sealed class Proof(IdiomState state, Block head, Guard guard)
    {
        private const int Depth = 32;
        private readonly Dictionary<Variable, Expr> definitions = state.function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        private readonly Dictionary<Variable, Block> owners = state.function.Blocks.SelectMany(b => b.Statements.OfType<Define>().Select(d => (d.Target, Block: b))).ToDictionary(p => p.Target, p => p.Block);
        private readonly Dictionary<Variable, bool> unchanged = [];
        private Func<Expr, TypeRef?>? types;
        private bool loadAfterStore;
        private Line? slow;

        public bool Holds(out string reason)
        {
            var fast = new Line();
            if (!Walk(fast, guard.Skip, false, null, out reason)) return false;
            var taken = new Line();
            slow = taken;
            var merge = fast.Merge;
            if (merge is null && fast.Exit is null) { reason = "快路径没有终点"; return false; }
            if (!Walk(taken, guard.Initialize, true, merge, out reason)) return false;
            // 同一标志的前一个守卫已经初始化时，这一臂的调用被清理掉，只剩写标志。
            if (!taken.Initialized && taken.FlagStore is null) { reason = "慢路径没有初始化"; return false; }
            if (loadAfterStore) { reason = "写入之后还有读取"; return false; }
            if (fast.Stores.Count != taken.Stores.Count || !fast.Stores.SequenceEqual(taken.Stores)) { reason = "两臂的写入不同"; return false; }
            if (merge is not null)
            {
                if (taken.Merge != merge) { reason = "两臂的汇合点不同"; return false; }
                var (a, b) = (merge.Predecessors.IndexOf(fast.Previous), merge.Predecessors.IndexOf(taken.Previous));
                if (a < 0 || b < 0) { reason = "两臂的汇合边不明"; return false; }
                foreach (var phi in merge.Statements.OfType<Phi>())
                {
                    var width = Observed(phi.Target, []);
                    if (width == 0 || phi.Sources.Length != merge.Predecessors.Count) continue;
                    var (skipped, initialized) = (Normal(new Use(phi.Sources[a], width), fast, 0), Normal(new Use(phi.Sources[b], width), taken, 0));
                    // 生成代码在守卫里只做初始化，不给局部赋值：这种 φ 只能来自 clang 的部分冗余消除，
                    // 快路径复用已有的值（不是读取），初始化可能改写内存的一臂重新读取。保留的正是重新读取的一臂。
                    // 两臂都是读取而位置不同时不成立。初始化调用破坏的寄存器不会再被真正读取，这一臂的值没有意义。
                    static bool Reads(Expr value) => ExprMap.Walk(value).Any(e => e is Load);
                    if (skipped != initialized && (Reads(skipped) || !Reads(initialized)) && initialized is not Use { Variable.Version: -1 })
                    { reason = "两臂的合流值不同"; return false; }
                }
                reason = "";
                return true;
            }
            if (taken.Exit is not { } after || fast.Exit is not { } normal) { reason = "两臂的终点不同"; return false; }
            var left = Normal(after.Condition, taken, 0);
            var right = Normal(normal.Condition, fast, 0);
            bool Same(Variable x, Variable y) => Normal(new Use(x, x.Width), taken, 0) == Normal(new Use(y, y.Width), fast, 0);
            bool Exit(ulong x, ulong y) => ClassGuardExits.Same(taken.Previous, x, fast.Previous, y, Same);
            if (left == right && Exit(after.Target, normal.Target) && Exit(after.Fallthrough, normal.Fallthrough)
                || left == Fold.Simplify(new Not(right)) && Exit(after.Target, normal.Fallthrough) && Exit(after.Fallthrough, normal.Target))
            {
                reason = "";
                return true;
            }
            reason = "两臂的出口分支不同";
            return false;
        }

        public void CommitMetadata(Branch branch)
        {
            var line = slow!;
            if (line.FlagStore is { } set && line.FlagBlock is { } block)
            {
                block.Statements[block.Statements.IndexOf(set)] = new Nop(set.Address, "MetadataInitGuard");
                state.initializedGuards.Add((block, guard.Flag));
            }
            state.Result.GuardSlots[guard.Flag] = [.. state.Result.GuardSlots.GetValueOrDefault(guard.Flag, []).Union(line.Slots).Order()];
            state.Result.InitializedSlots.UnionWith(line.Slots);
            state.Result.MetadataGuardBranches.Add(branch.Address);
            state.Result.Hit(Template.MetadataInitGuard);
        }

        private bool Walk(Line line, Block start, bool initializing, Block? stop, out string reason)
        {
            reason = "";
            var visited = new HashSet<Block>();
            var (previous, current) = (head, start);
            while (true)
            {
                // 快路径止于第一个其他路径也进入的块，慢路径走到同一点。
                if (current == stop || !initializing && current.Predecessors.Count > 1)
                {
                    line.Previous = previous;
                    line.Merge = current;
                    return true;
                }
                // 没有异常边只说明块里没有原生抛出点，不说明它在 try 外：只有两处都有异常边且去向不同才算跨区域。
                if (!visited.Add(current) || current.IsLandingPad || current.Handler is not null && head.Handler is not null && current.Handler != head.Handler)
                { reason = "路径含异常边或环"; return false; }
                line.Previous = previous;
                var incoming = current.Predecessors.IndexOf(previous);
                var shared = current.Predecessors.Count > 1;
                Block? onward = null;
                foreach (var statement in current.Statements)
                {
                    switch (statement)
                    {
                        case Nop or Jump:
                            break;
                        case Phi phi:
                            if (incoming < 0 || phi.Sources.Length != current.Predecessors.Count) { reason = "路径上的 φ 不明"; return false; }
                            line.Values[phi.Target] = Normal(new Use(phi.Sources[incoming], phi.Target.Width), line, 0);
                            break;
                        // 快路径直接到达汇合点，初始化一臂重新读取之后多一次抛出判断（判空、越界）：
                        // 快路径的值已经判过，保留这一臂时判断照常执行，结果相同。
                        case Branch when initializing && stop is not null && !shared && Survivor(current) is { } continuing:
                            onward = continuing;
                            break;
                        case Branch exit when !shared:
                            line.Previous = current;
                            line.Exit = exit;
                            return true;
                        case Define define when !shared && !ExprMap.Walk(define.Value).Any(e => e is Intrinsic or Unknown):
                            line.Values[define.Target] = Normal(define.Value, line, 0);
                            break;
                        case Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } set when initializing && guard.Kind == Kind.Metadata && target.Value == guard.Flag:
                            line.FlagStore = set;
                            line.FlagBlock = current;
                            break;
                        case Store store when !shared && !ExprMap.Walk(store.Value).Concat(ExprMap.Walk(store.Target)).Any(e => e is Intrinsic or Unknown):
                            line.Stores.Add((Normal(store.Target, line, 0), Normal(store.Value, line, 0)));
                            break;
                        case Call call when initializing && Initializes(call, line):
                            line.Initialized = true;
                            break;
                        case Call { Op.Kind: OpKind.NullCheck, Arguments: [var subject] } when !shared && (initializing || Checked(Normal(subject, line, 0), line)):
                            // 初始化一臂重新读取之后再判空，快路径复用已判过的值：保留这一臂时判空照常执行，结果相同。
                            break;
                        default:
                            reason = $"路径上有其他语句 0x{statement.Address:x}";
                            return false;
                    }
                }
                if (onward is not null) { (previous, current) = (current, onward); continue; }
                if (current.NormalSuccessors.ToArray() is not [var next]) { reason = "路径没有唯一后继"; return false; }
                (previous, current) = (current, next);
            }
        }

        /// <summary>分支的一侧只抛出（以不返回的调用结束）时，另一侧是继续执行的路径。</summary>
        private static Block? Survivor(Block block)
        {
            static bool Throws(Block target) => !target.NormalSuccessors.Any() && target.Statements.LastOrDefault() is Call { DoesNotReturn: true };
            return block.NormalSuccessors.ToArray() is [var first, var second] && first != second
                ? Throws(first) && !Throws(second) ? second : Throws(second) && !Throws(first) ? first : null
                : null;
        }

        private bool Initializes(Call call, Line line)
        {
            var helper = state.owner.HelperOf(call)?.Kind;
            switch (guard.Kind)
            {
                case Kind.Metadata:
                    if (helper != HelperKind.InitMetadata || call.Arguments.FirstOrDefault() is not { } slot || Normal(slot, line, 0) is not Const address
                        || state.facts.Usages.At(address.Value) is null) return false;
                    line.Slots.Add(address.Value);
                    return true;
                case Kind.ClassConstructor:
                    return call.Op is { Kind: OpKind.RunClassConstructor } op ? Equals(op.Operand, guard.Type) : helper == HelperKind.ClassInit && Class(call, line);
                default:
                    if (call.Op is { Kind: OpKind.InitClass } init ? !Equals(init.Operand, guard.Type) : !(helper == HelperKind.InitializedTypeInfo && Class(call, line))) return false;
                    // 初始化返回类本身。
                    if (call.Defines is [{ } result, ..]) line.Values[result] = new Symbol(SymbolKind.Class, guard.Type!);
                    return true;
            }
        }

        private bool Class(Call call, Line line) => call.Arguments.FirstOrDefault() is { } argument
            && Normal(argument, line, 0) is Symbol { Kind: SymbolKind.Class, Value: var type } && Equals(type, guard.Type);

        /// <summary>归一为守卫处的内容：路径上的定义代入，读取经守卫之前的写入转发；被改写过的旧读取保持为变量。</summary>
        private Expr Normal(Expr expression, Line line, int depth)
        {
            if (depth > Depth) return expression;
            return Fold.Simplify(ExprMap.Map(expression, part =>
            {
                switch (part)
                {
                    case Use use:
                        {
                            Expr value;
                            if (line.Values.TryGetValue(use.Variable, out var known)) value = known;
                            else if (line.Expanded.TryGetValue(use.Variable, out var expanded)) value = expanded;
                            else if (definitions.TryGetValue(use.Variable, out var source)
                                && (!ExprMap.Walk(source).Any(e => e is Load) || Unchanged(use.Variable, source)))
                                value = line.Expanded[use.Variable] = Normal(source, line, depth + 1);
                            else return null;
                            return value.Width == use.Width ? value : Fold.Convert(ConvKind.Truncate, value, use.Width);
                        }
                    case Load load:
                        if (line.Stores.Count > 0) loadAfterStore = true;
                        return Content(new Load(Normal(load.Address, line, depth + 1), load.Width), line, depth + 1);
                    default:
                        return null;
                }
            }));
        }

        /// <summary>守卫之前覆盖这段内存的写入给出它的值；遇到可能改写的语句就停止转发。</summary>
        private Expr Content(Load load, Line line, int depth)
        {
            var (root, offset) = SplitPass.Split(load.Address);
            var bytes = (ulong)load.Width / 8;
            foreach (var statement in Before())
            {
                if (statement is Store store)
                {
                    var (written, at) = SplitPass.Split(Normal(store.Target, line, depth + 1));
                    var size = (ulong)store.Value.Width / 8;
                    if (written == root && offset >= at && offset - at + bytes <= size)
                        return Fold.Extract(Normal(store.Value, line, depth + 1), checked((int)(offset - at) * 8), load.Width);
                    if (!Disjoint(written, at, size, root, offset, bytes)) return load;
                }
                else if (statement is Call call && !KeepsMemory(call)) return load;
            }
            return load;
        }

        /// <summary>变量读取的内存从读取处到守卫，每条路径上都没有被改写。</summary>
        private bool Unchanged(Variable variable, Expr source)
        {
            if (unchanged.TryGetValue(variable, out var known)) return known;
            return unchanged[variable] = Prove(variable, source);
        }

        private bool Prove(Variable variable, Expr source)
        {
            if (!owners.TryGetValue(variable, out var owner)) return false;
            var reads = ExprMap.Walk(source).OfType<Load>().Select(l => SplitPass.Split(state.defs.Expand(l.Address)) is var (root, offset) ? (Root: root, Offset: offset, Bytes: (ulong)l.Width / 8) : default).ToArray();
            bool Keeps(Stmt statement) => statement switch
            {
                Store store => SplitPass.Split(state.defs.Expand(store.Target)) is var (written, at)
                    && reads.All(r => Disjoint(written, at, (ulong)store.Value.Width / 8, r.Root, r.Offset, r.Bytes)),
                Call call => KeepsMemory(call),
                _ => true,
            };
            var visited = new HashSet<Block>();
            var pending = new Stack<Block>();
            pending.Push(head);
            while (pending.TryPop(out var block))
            {
                if (!visited.Add(block)) continue;
                if (block == owner)
                {
                    var from = block.Statements.FindIndex(s => s is Define define && define.Target == variable);
                    if (!block.Statements.Skip(from + 1).All(Keeps)) return false;
                    continue;
                }
                if (block.IsLandingPad || block == state.function.EntryBlock || !block.Statements.All(Keeps)) return false;
                foreach (var predecessor in block.Predecessors) pending.Push(predecessor);
            }
            return true;
        }

        private bool Checked(Expr subject, Line line)
        {
            foreach (var statement in Before())
                if (statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var value] } && Normal(value, line, Depth / 2) == subject) return true;
            return false;
        }

        /// <summary>从守卫沿唯一前驱向前的语句。</summary>
        private IEnumerable<Stmt> Before()
        {
            var visited = new HashSet<Block>();
            var block = head;
            while (visited.Add(block))
            {
                for (var i = block.Statements.Count - 1; i >= 0; i--) yield return block.Statements[i];
                if (block.IsLandingPad || block.Predecessors is not [var previous]) yield break;
                block = previous;
            }
        }

        private bool KeepsMemory(Call call) => call.Op is { } op ? RuntimeOps.Of(op.Kind)?.Behavior.InvalidatesMemory == false
            : state.owner.HelperOf(call)?.Kind is HelperKind.InitMetadata or HelperKind.InitializedTypeInfo;

        private bool Disjoint(Expr written, ulong at, ulong size, Expr root, ulong offset, ulong bytes)
        {
            var separate = offset + bytes <= at || at + size <= offset;
            if (written == root) return separate;
            // 栈与元数据不是对象字段；托管引用只指向对象起点，不同偏移的字段不重叠。
            if (written is FrameAddress != root is FrameAddress) return true;
            if (written is Symbol || root is Symbol) return false;
            types ??= DelegateCallNormalizer.TypeQuery(state.facts, state.function);
            return separate && at >= RuntimeLayout.ObjectHeaderSize && offset >= RuntimeLayout.ObjectHeaderSize
                && types(written) is { } a && ManagedTypes.IsReferenceType(a) && types(root) is { } b && ManagedTypes.IsReferenceType(b);
        }

        private int Observed(Variable variable, HashSet<Variable> seen)
        {
            if (!seen.Add(variable)) return 0;
            var statements = state.function.Blocks.SelectMany(b => b.Statements).ToArray();
            var used = statements.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Use>().Where(u => u.Variable == variable).Select(u => u.Width).DefaultIfEmpty(0).Max();
            return Math.Max(used, statements.OfType<Phi>().Where(p => p.Sources.Contains(variable)).Select(p => Observed(p.Target, seen)).DefaultIfEmpty(0).Max());
        }
    }
}
