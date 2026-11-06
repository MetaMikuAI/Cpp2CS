using System.Collections.Immutable;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Recovery.Effects;
using Cpp2CS.Recovery.Lowering;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// il2cpp::utils::Finally 的逆。C++ 里 finally 是析构函数：catch 把异常存进闭包，离开作用域时运行处理体，异常不为空就重新抛出。
/// clang 把它展开成存异常的局部和 cleanup.dest.slot（下面称去向局部），再按路径复制合并。两种形态都等于 try/finally（ECMA-335 I.12.4.2），条件是：
/// catch 除了运行处理体再抛出同一个异常之外什么都不做；try 的每个出口都运行同样的处理体，然后继续。
/// 判定按路径求值，不看块的形状：沿路径把这两种局部当作已知常量折叠条件，同步比较 catch 路径和每个出口路径上的语句。
/// catch 路径到达“抛出异常”时，出口路径所在的位置就是 leave 的目标。不满足条件的 catch 保持原样。
/// 区域的 try 只覆盖能抛出的块，循环里不抛出的块在 try 之外，出口又回到 try：这些块并入 try（异常不会从那里发生），于是 try 包住整个循环。
/// catch 路径上写给后续代码的复制在抛出之后没有读者，只要处理体不读它们就可以丢弃。
/// 还原之后只为异常到达而赋值的局部不再有读者，局部可以再合并一次。
/// 还原后处理体里的异常和重新抛出的异常都走 try 外层的区域，所以路径上能抛出的语句必须和 try 在同样的外层区域里。
/// 异步状态机挂起时不运行 finally：处理体开头判断状态局部，挂起路径上 clang 把它折叠掉了，出口路径直接到目标。调用方说明哪些语句是挂起，这样的出口不比较处理体。
/// </summary>
public static class FinallyRecovery
{
    /// <summary>处理体最多的语句与分支数；再多就不是 finally 的展开。</summary>
    private const int Budget = 128;
    /// <summary>新块的地址不对应原生代码，取高位以免与原生块和 try 分派块重合。</summary>
    private const ulong SyntheticAddress = 3UL << 62;

    /// <param name="state">挂起时写成非负值的状态局部。</param>
    /// <param name="suspends">语句是挂起调用。</param>
    public static ManagedBody Run(ManagedBody body, Variable? state = null, Func<ManagedStatement, bool>? suspends = null)
    {
        if (body.Regions.All(r => r.Kind != ManagedRegionKind.Catch)) return body;
        // 方法体可能已经还原过一轮，新块不能和已有的同址。
        var next = body.Blocks.Select(b => b.Address).Where(a => a >> 62 == SyntheticAddress >> 62).Select(a => ((a ^ SyntheticAddress) >> 40) + 1).DefaultIfEmpty(0UL).Max();
        var tried = new HashSet<ulong>();
        var changed = false;
        // 从内向外：外层的 try 里可能有已经还原的内层 finally。
        while (body.Regions.Where(r => r.Kind == ManagedRegionKind.Catch && !tried.Contains(r.HandlerEntry)).OrderBy(r => r.Try.Count).FirstOrDefault() is { } region)
        {
            tried.Add(region.HandlerEntry);
            if (new Recovery(body, region, () => SyntheticAddress | next++ << 40, state, suspends).Run() is not { } recovered) continue;
            body = recovered;
            changed = true;
        }
        return changed ? EnumeratorForms.Run(LocalCoalescing.Run(body)) : body;
    }

    /// <summary>路径上已知的局部：常量，或者 null 表示当前异常（非空，具体值无关）。</summary>
    private sealed record Cursor(ulong Block, int Index, ImmutableDictionary<Variable, ConstantValue?> Known);

    private sealed class Recovery(ManagedBody body, ManagedRegion region, Func<ulong> fresh, Variable? state, Func<ManagedStatement, bool>? suspends)
    {
        private readonly Dictionary<ulong, ManagedBlock> blocks = body.Blocks.ToDictionary(b => b.Address);
        private readonly List<ManagedBlock> handler = [];
        private readonly Dictionary<ulong, ManagedBlock> built = [];
        private HashSet<Variable> holders = [];
        private HashSet<Variable> destinations = [];
        private readonly Dictionary<Variable, LocalValue> destinationLocals = [];
        private readonly HashSet<Variable> dropped = [];
        private readonly HashSet<Variable> renamed = [];
        private ulong? end;
        private int budget = Budget;
        /// <summary>包住整个 try 的其他区域。</summary>
        private readonly HashSet<ManagedRegion> outer = body.Regions.Where(r => !ReferenceEquals(r, region) && region.Try.All(r.Try.Contains)).ToHashSet();

        private bool SameScope(ulong block) => body.Regions.Where(r => !ReferenceEquals(r, region) && r.Try.Contains(block)).ToHashSet().SetEquals(outer);

        /// <summary>语句留在原位时异常的去向，和移进处理体之后相同。</summary>
        private bool Portable(ManagedStatement statement, ulong block) => !ManagedEffects.Statement(statement).MayThrow || SameScope(block);

        public ManagedBody? Run()
        {
            if (region.Exception is not { } caught || region.CatchType is not null) return null;
            if (Holders(caught.Variable) is not { } found) return null;
            holders = found;
            destinations = Destinations();
            var start = new Cursor(region.HandlerEntry, 0, ImmutableDictionary<Variable, ConstantValue?>.Empty.Add(caught.Variable, null));
            if (Build(start, []) is not { } entry || handler.Count <= 1) return null;
            // 丢弃的复制写的局部，处理体要读就不能丢。
            if (handler.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => dropped.Contains(l.Variable))) return null;
            if (Nested() is { } nested && Exits(nested, entry) is { } all && Rewrite(entry, nested, all) is { } whole) return whole;
            if (Exits(region.Try, entry) is { } exits) return Rewrite(entry, region.Try, exits);
            return Extended() is { } extended && Exits(extended, entry) is { } wider ? Rewrite(entry, extended, wider) : null;
        }

        private Dictionary<ManagedEdge, ManagedEdge>? Exits(IReadOnlyList<ulong> tryBlocks, ulong entry)
        {
            var inTry = tryBlocks.ToHashSet();
            var exits = new Dictionary<ManagedEdge, ManagedEdge>(ReferenceEqualityComparer.Instance);
            var skips = SkipsWhenSuspended(entry);
            foreach (var address in tryBlocks)
            {
                var suspended = skips && suspends!= null && blocks[address].Statements.Any(suspends);
                foreach (var statement in blocks[address].Statements)
                {
                    if (statement is ManagedEndFault || statement is ManagedReturn && !suspended) return null;
                    foreach (var edge in ManagedValues.Edges(statement).Where(e => !inTry.Contains(e.Target)))
                    {
                        if ((suspended ? Direct(edge) : Exit(edge, entry)) is not { } rewritten) return null;
                        exits[edge] = rewritten;
                    }
                }
            }
            return exits.Count == 0 ? null : exits;
        }

        /// <summary>处理体的第一条语句判断状态局部，非负时直接结束。</summary>
        private bool SkipsWhenSuspended(ulong entry)
        {
            if (state is not { } variable || !built.TryGetValue(entry, out var first) || first.Statements is not [ManagedBranch { Condition: ComparisonValue { Left: LocalValue left, Right: ConstantValue { Bits: 0 } } guard } branch] || !left.Variable.Equals(variable)) return false;
            var skipped = guard.Condition switch
            {
                Cond.Sge => branch.Taken.Target,
                Cond.Slt => branch.Fallthrough.Target,
                _ => (ulong?)null,
            };
            return skipped is { } target && built.TryGetValue(target, out var next) && next.Statements is [ManagedEndFault];
        }

        /// <summary>挂起路径的出口：不运行处理体，直接到 leave 的目标。</summary>
        private ManagedEdge? Direct(ManagedEdge edge)
        {
            var match = new ExitMatch();
            var real = new List<ManagedCopy>();
            var known = Follow(edge, ImmutableDictionary<Variable, ConstantValue?>.Empty, real);
            match.Before.AddRange(real);
            real = [];
            if (Settle(new(edge.Target, 0, known), real) is not var (final, _) || final.Index != 0 || real.Any(c => !Movable(c))) return null;
            match.Before.AddRange(real);
            match.Target = (final.Block, final.Known);
            return Finish(match);
        }

        /// <summary>
        /// try { try { X } catch (E) { H } } finally { F } 的落地块是串起来的：X 的异常到 E 的处理块，处理块里再抛出的才到这个 catch，
        /// 所以这个区域的 try 只有 H。try 在别的 catch 的处理块里时，把那个 catch 整个算进 try：它的异常最后都经过这里，出口由 Exits 核对。
        /// </summary>
        private List<ulong>? Nested()
        {
            var included = region.Try.ToHashSet();
            var grown = false;
            for (var changed = true; changed;)
            {
                changed = false;
                foreach (var other in body.Regions.Where(r => !ReferenceEquals(r, region) && r.Kind == ManagedRegionKind.Catch))
                    if (included.All(other.Handler.Contains))
                    {
                        included.UnionWith(other.Try);
                        included.UnionWith(other.Handler);
                        changed = grown = true;
                    }
            }
            if (!grown) return null;
            included.ExceptWith(region.Handler);
            var targets = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (From: b.Address, e.Target))).ToArray();
            if (targets.Where(e => included.Contains(e.Target) && !included.Contains(e.From)).Select(e => e.Target).Distinct().ToArray() is not [var first]) return null;
            var positions = body.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
            return included.Where(a => a != first && positions.ContainsKey(a)).OrderBy(a => positions[a]).Prepend(first).ToList();
        }

        /// <summary>
        /// 并入 try 的块：从 try 的出口可达、又能回到 try，不经过处理块。C++ 作用域的出口都运行处理体，所以走这条路径时还在作用域里；
        /// 这些块没有异常边，说明 clang 证明了其中的调用不会抛出，读取和元素访问也已经检查过，并入 try 不改变行为。
        /// 显式的抛出和检查说明块实际在作用域之外。结果的第一个块是唯一的外部入口。
        /// </summary>
        private List<ulong>? Extended()
        {
            var inTry = region.Try.ToHashSet();
            var excluded = region.Handler.ToHashSet();
            var predecessors = new Dictionary<ulong, List<ulong>>();
            foreach (var block in body.Blocks)
                foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges))
                    (predecessors.TryGetValue(edge.Target, out var list) ? list : predecessors[edge.Target] = []).Add(block.Address);
            var forward = new HashSet<ulong>();
            var work = new Stack<ulong>(region.Try.SelectMany(a => blocks[a].Statements).SelectMany(ManagedValues.Edges).Select(e => e.Target)
                .Where(t => !inTry.Contains(t) && !excluded.Contains(t)));
            while (work.TryPop(out var address))
                if (forward.Add(address) && blocks.TryGetValue(address, out var block))
                    foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges))
                        if (!inTry.Contains(edge.Target) && !excluded.Contains(edge.Target)) work.Push(edge.Target);
            var between = new HashSet<ulong>();
            work = new Stack<ulong>(region.Try.SelectMany(a => predecessors.GetValueOrDefault(a) ?? []).Where(forward.Contains));
            while (work.TryPop(out var address))
                if (between.Add(address))
                    foreach (var predecessor in predecessors.GetValueOrDefault(address) ?? [])
                        if (forward.Contains(predecessor)) work.Push(predecessor);
            if (between.Count == 0 || between.Any(a => blocks[a].Statements.Any(Throws))) return null;
            // 其他区域要么同时包含这些块和 try，要么都不包含。
            foreach (var other in body.Regions.Where(r => !ReferenceEquals(r, region)))
            {
                bool Consistent(IReadOnlyList<ulong> list) => list.Contains(region.Try[0]) ? between.All(list.Contains) : !between.Any(list.Contains);
                if (!Consistent(other.Try) || !Consistent(other.Handler)) return null;
            }
            var all = inTry.Concat(between).ToHashSet();
            var entries = all.Where(a => (predecessors.GetValueOrDefault(a) ?? []).Any(p => !all.Contains(p))).ToArray();
            if (entries is not [var first]) return null;
            var positions = body.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
            return all.Where(a => a != first).OrderBy(a => positions[a]).Prepend(first).ToList();
        }

        private static bool Throws(ManagedStatement statement) => statement switch
        {
            ManagedThrow or ManagedRethrow or ManagedCheck or ManagedHole => true,
            ManagedCall => false,
            _ => (ManagedEffects.Statement(statement).Exceptions & ExceptionEffect.Other) != 0,
        };

        /// <summary>
        /// 保存当前异常的局部。它们只能取异常、取其他这样的局部或空值，只用来和空比较、抛出或再传给同类局部：
        /// 有其他用途时异常被观察了，这不是 finally。
        /// </summary>
        private HashSet<Variable>? Holders(Variable caught)
        {
            var found = new HashSet<Variable> { caught };
            var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
            var copies = statements.SelectMany(s => ManagedValues.Edges(s).SelectMany(e => e.Copies).Select(c => (c.Target, c.Value))
                .Concat(s is ManagedAssignment a ? [(a.Target, a.Value)] : [])).ToArray();
            for (var changed = true; changed;)
            {
                changed = false;
                foreach (var (target, value) in copies)
                    if (value is LocalValue source && found.Contains(source.Variable) && found.Add(target.Variable)) changed = true;
            }
            foreach (var (target, value) in copies)
                if (found.Contains(target.Variable) && value is not (LocalValue or ConstantValue { Bits: 0 })) return null;
            foreach (var statement in statements)
            {
                if (statement is ManagedCall { Result: { } result } && found.Contains(result.Variable)) return null;
                var values = statement switch
                {
                    ManagedAssignment { Value: LocalValue } => [],
                    ManagedThrow { Exception: LocalValue } => [],
                    ManagedBranch { Condition: var condition } when NullTest(condition, found) => [],
                    _ => ManagedValues.Of(statement),
                };
                if (values.SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => found.Contains(l.Variable))) return null;
                foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies))
                    if (copy.Value is not LocalValue && ManagedValues.Walk(copy.Value).OfType<LocalValue>().Any(l => found.Contains(l.Variable))) return null;
            }
            return found;
        }

        private static bool NullTest(ManagedValue condition, HashSet<Variable> locals) => condition switch
        {
            NegatedValue negated => NullTest(negated.Operand, locals),
            ComparisonValue { Condition: Cond.Eq or Cond.Ne, Left: LocalValue left, Right: ConstantValue { Bits: 0 } } => locals.Contains(left.Variable),
            LocalValue local => locals.Contains(local.Variable),
            _ => false,
        };

        /// <summary>去向局部：只取常量，只在和常量的运算（switch 降级成范围检查和位测试）里比较，或作为 switch 的下标。</summary>
        private HashSet<Variable> Destinations()
        {
            var candidates = new HashSet<Variable>();
            var excluded = new HashSet<Variable>();
            void Exclude(ManagedValue value) => excluded.UnionWith(ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable));
            foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
            {
                switch (statement)
                {
                    case ManagedAssignment { Target: var target, Value: ConstantValue }: candidates.Add(target.Variable); destinationLocals[target.Variable] = target; break;
                    case ManagedAssignment { Target: var target, Value: var value }: excluded.Add(target.Variable); Exclude(value); break;
                    case ManagedCall { Result: { } result } call: excluded.Add(result.Variable); foreach (var value in ManagedValues.Of(call)) Exclude(value); break;
                    case ManagedBranch { Condition: ComparisonValue comparison } when OverOneLocal(comparison): break;
                    case ManagedSwitch { Index: LocalValue }: break;
                    default: foreach (var value in ManagedValues.Of(statement)) Exclude(value); break;
                }
                foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies))
                {
                    if (copy.Value is ConstantValue) { candidates.Add(copy.Target.Variable); destinationLocals[copy.Target.Variable] = copy.Target; }
                    else { excluded.Add(copy.Target.Variable); Exclude(copy.Value); }
                }
            }
            candidates.ExceptWith(excluded);
            candidates.ExceptWith(holders);
            return candidates;
        }

        private static bool OverOneLocal(ManagedValue value)
        {
            var walked = ManagedValues.Walk(value).ToArray();
            return walked.All(v => v is LocalValue or ConstantValue or BinaryValue or ComparisonValue or ConversionValue)
                && walked.OfType<LocalValue>().Select(l => l.Variable).Distinct().Count() == 1;
        }

        private static bool? Fold(ManagedValue condition, ImmutableDictionary<Variable, ConstantValue?> known) => condition switch
        {
            NegatedValue negated => !Fold(negated.Operand, known),
            LocalValue local when known.TryGetValue(local.Variable, out var value) => value is null || value.Bits != 0,
            ComparisonValue { Condition: var cond and (Cond.Eq or Cond.Ne), Left: LocalValue left, Right: ConstantValue right } when known.TryGetValue(left.Variable, out var value) =>
                // 当前异常不是空。和其他常量比较的不是保存异常的局部。
                value is null ? (right.Bits == 0 ? cond == Cond.Ne : null) : (value.Bits == right.Bits) == (cond == Cond.Eq),
            ComparisonValue comparison when OverOneLocal(comparison) => ConstantConditions.Evaluate(comparison, leaf =>
                leaf is LocalValue local && known.TryGetValue(local.Variable, out var value) && value is { Width: <= 32 } ? (int)value.Bits : null) is { } result ? result != 0 : null,
            _ => null,
        };

        private bool Tracked(Variable variable) => holders.Contains(variable) || destinations.Contains(variable);

        private ImmutableDictionary<Variable, ConstantValue?> Follow(ManagedEdge edge, ImmutableDictionary<Variable, ConstantValue?> known, List<ManagedCopy> real)
        {
            var result = known;
            foreach (var copy in edge.Copies)
            {
                if (copy.Value is ConstantValue constant && Tracked(copy.Target.Variable)) result = result.SetItem(copy.Target.Variable, constant);
                else if (copy.Value is LocalValue source && holders.Contains(copy.Target.Variable))
                    result = known.TryGetValue(source.Variable, out var value) ? result.SetItem(copy.Target.Variable, value) : result.Remove(copy.Target.Variable);
                else real.Add(copy);
            }
            return result;
        }

        /// <summary>走到下一条路径上真正要执行的语句：折叠已知的条件，跳过已知局部的赋值。</summary>
        private (Cursor Cursor, ManagedStatement Statement)? Settle(Cursor cursor, List<ManagedCopy> real)
        {
            for (var steps = 0; steps < Budget; steps++)
            {
                if (!blocks.TryGetValue(cursor.Block, out var block) || cursor.Index >= block.Statements.Count) return null;
                var statement = block.Statements[cursor.Index];
                switch (statement)
                {
                    case ManagedAssignment { Target: var target, Value: ConstantValue constant } when Tracked(target.Variable):
                        cursor = cursor with { Index = cursor.Index + 1, Known = cursor.Known.SetItem(target.Variable, constant) };
                        continue;
                    case ManagedAssignment { Target: var target, Value: LocalValue source } when holders.Contains(target.Variable):
                        cursor = cursor with
                        {
                            Index = cursor.Index + 1,
                            Known = cursor.Known.TryGetValue(source.Variable, out var value) ? cursor.Known.SetItem(target.Variable, value) : cursor.Known.Remove(target.Variable),
                        };
                        continue;
                    case ManagedJump jump:
                        cursor = new(jump.Edge.Target, 0, Follow(jump.Edge, cursor.Known, real));
                        continue;
                    case ManagedBranch branch when Fold(branch.Condition, cursor.Known) is { } taken:
                        var edge = taken ? branch.Taken : branch.Fallthrough;
                        cursor = new(edge.Target, 0, Follow(edge, cursor.Known, real));
                        continue;
                    case ManagedSwitch { Index: LocalValue index } table when cursor.Known.TryGetValue(index.Variable, out var selected) && selected is not null:
                        if (selected.Bits >= (ulong)table.Cases.Count) return null;
                        var chosen = table.Cases[(int)selected.Bits];
                        cursor = new(chosen.Target, 0, Follow(chosen, cursor.Known, real));
                        continue;
                    default:
                        return (cursor, statement);
                }
            }
            return null;
        }

        private ulong End()
        {
            if (end is { } existing) return existing;
            var address = fresh();
            end = address;
            return address;
        }

        /// <summary>沿 catch 路径构造处理体，返回入口地址。路径必须都到达“抛出当前异常”。</summary>
        private ulong? Build(Cursor cursor, HashSet<(ulong, int)> open)
        {
            if (--budget < 0) return null;
            var real = new List<ManagedCopy>();
            if (Settle(cursor, real) is not var (at, statement)) return null;
            Drop(real);
            var key = (at.Block, at.Index);
            switch (statement)
            {
                case ManagedThrow { Exception: LocalValue thrown } when holders.Contains(thrown.Variable) && at.Known.TryGetValue(thrown.Variable, out var value) && value is null:
                case ManagedRethrow:
                    return SameScope(at.Block) ? Ending() : null;
                case ManagedReturn or ManagedThrow or ManagedEndFault or ManagedSwitch or ManagedHole:
                    return null;
            }
            if (!Portable(statement, at.Block) || !open.Add(key)) return null;
            var address = fresh();
            var slot = handler.Count;
            handler.Add(null!);
            ManagedBlock? block = null;
            if (statement is ManagedBranch branch)
            {
                var (takenReal, fallthroughReal) = (new List<ManagedCopy>(), new List<ManagedCopy>());
                var taken = Build(new(branch.Taken.Target, 0, Follow(branch.Taken, at.Known, takenReal)), open);
                var fallthrough = Build(new(branch.Fallthrough.Target, 0, Follow(branch.Fallthrough, at.Known, fallthroughReal)), open);
                Drop(takenReal);
                Drop(fallthroughReal);
                if (taken is { } t && fallthrough is { } f)
                    block = new ManagedBlock(address, [branch with { Taken = new(t, []), Fallthrough = new(f, []) }]);
            }
            else if (Build(at with { Index = at.Index + 1 }, open) is { } next)
                block = new ManagedBlock(address, [statement, new ManagedJump(statement.Address, new(next, []))]);
            open.Remove(key);
            if (block is null) return null;
            handler[slot] = block;
            built[address] = block;
            return address;
        }

        private void Drop(List<ManagedCopy> copies) => dropped.UnionWith(copies.Select(c => c.Target.Variable));

        private ulong Ending()
        {
            var address = End();
            if (!built.ContainsKey(address))
            {
                var block = new ManagedBlock(address, [new ManagedEndFault(region.HandlerEntry)]);
                built[address] = block;
                handler.Add(block);
            }
            return address;
        }

        private sealed class ExitMatch
        {
            public readonly List<ManagedCopy> Before = [];
            public bool Started;
            public (ulong Block, ImmutableDictionary<Variable, ConstantValue?> Known)? Target;
            /// <summary>出口路径上的局部对应处理体里的哪个局部。</summary>
            public readonly Dictionary<Variable, LocalValue> Renamed = [];
        }

        /// <summary>
        /// 同一条语句在两条路径上可以写不同的局部（clang 给每个副本一个临时变量）。这些局部此后不能再被处理体之外读取，改写完再核对。
        /// </summary>
        private bool Equivalent(ManagedStatement mine, ManagedStatement theirs, ExitMatch match)
        {
            ManagedValue Rename(ManagedValue value) => value is LocalValue local
                ? match.Renamed.TryGetValue(local.Variable, out var name) ? name : local
                : ManagedValues.Map(value, Rename);
            LocalValue? Bind(LocalValue? a, LocalValue? b)
            {
                if (a is null || b is null || a.Variable.Equals(b.Variable) || !a.Type.Equals(b.Type) || a.Width != b.Width) return b;
                if (match.Renamed.TryGetValue(b.Variable, out var existing)) return existing;
                match.Renamed[b.Variable] = a;
                renamed.Add(b.Variable);
                return a;
            }
            ManagedStatement translated = theirs switch
            {
                ManagedAssignment assignment when mine is ManagedAssignment m => assignment with { Target = Bind(m.Target, assignment.Target)!, Value = Rename(assignment.Value) },
                ManagedCall call when mine is ManagedCall m => call with { Result = Bind(m.Result, call.Result) },
                _ => theirs,
            };
            if (translated is not ManagedAssignment) translated = ManagedValues.Map(translated, Rename);
            return ManagedStructure.Same(mine with { Address = 0 }, translated with { Address = 0 });
        }

        /// <summary>出口路径和处理体同步走，得到 leave 的目标和要留在出口上的复制。</summary>
        private ManagedEdge? Exit(ManagedEdge edge, ulong entry)
        {
            var match = new ExitMatch();
            var real = new List<ManagedCopy>();
            var known = Follow(edge, ImmutableDictionary<Variable, ConstantValue?>.Empty, real);
            match.Before.AddRange(real);
            return Match(entry, new(edge.Target, 0, known), match) ? Finish(match) : null;
        }

        private ManagedEdge? Finish(ExitMatch match)
        {
            if (match.Target is not { } target) return null;
            // 这些复制原本在处理体之前依次发生，放到同一条边上要没有依赖。
            var before = match.Before;
            for (var i = 0; i < before.Count; i++)
                for (var j = i + 1; j < before.Count; j++)
                    if (before[i].Target.Variable.Equals(before[j].Target.Variable)
                        || ManagedValues.Walk(before[j].Value).OfType<LocalValue>().Any(l => l.Variable.Equals(before[i].Target.Variable))) return null;
            // 后面可能还要读去向局部，它们在原路径上的值写到出口上；处理体不读它们。
            var kept = target.Known.Where(p => destinations.Contains(p.Key) && p.Value is not null)
                .Select(p => new ManagedCopy(destinationLocals[p.Key], p.Value!));
            return new ManagedEdge(target.Block, before.Concat(kept).ToArray());
        }

        private bool Match(ulong at, Cursor cursor, ExitMatch match)
        {
            foreach (var statement in built[at].Statements)
            {
                var real = new List<ManagedCopy>();
                switch (statement)
                {
                    case ManagedJump jump:
                        return Match(jump.Edge.Target, cursor, match);
                    case ManagedEndFault:
                    {
                        if (Settle(cursor, real) is not var (final, _) || final.Index != 0) return false;
                        if (match.Target is { } existing && existing.Block != final.Block) return false;
                        if (real.Any(c => !Movable(c))) return false;
                        match.Before.AddRange(real);
                        match.Target = (final.Block, final.Known);
                        return true;
                    }
                    case ManagedBranch branch:
                    {
                        if (Settle(cursor, real) is not var (position, current) || current is not ManagedBranch other) return false;
                        if (!Keep(real, match)) return false;
                        match.Started = true;
                        var (taken, fallthrough) = ManagedStructure.Value(branch.Condition, other.Condition) ? (other.Taken, other.Fallthrough)
                            : Opposite(branch.Condition, other.Condition) ? (other.Fallthrough, other.Taken) : (null!, null!);
                        if (taken is null) return false;
                        var (takenReal, fallthroughReal) = (new List<ManagedCopy>(), new List<ManagedCopy>());
                        var takenKnown = Follow(taken, position.Known, takenReal);
                        var fallthroughKnown = Follow(fallthrough, position.Known, fallthroughReal);
                        return takenReal.Count == 0 && fallthroughReal.Count == 0
                            && Match(branch.Taken.Target, new(taken.Target, 0, takenKnown), match)
                            && Match(branch.Fallthrough.Target, new(fallthrough.Target, 0, fallthroughKnown), match);
                    }
                    default:
                    {
                        if (Settle(cursor, real) is not var (position, current) || !Portable(current, position.Block) || !Keep(real, match) || !Equivalent(statement, current, match)) return false;
                        match.Started = true;
                        cursor = position with { Index = position.Index + 1 };
                        break;
                    }
                }
            }
            return false;
        }

        /// <summary>处理体之后的复制可以提到出口上：值只读局部和常量，处理体既不读它的目标，也不改写它读的局部。</summary>
        private bool Movable(ManagedCopy copy)
        {
            if (ManagedValues.Walk(copy.Value).Any(v => v is not (LocalValue or ConstantValue))) return false;
            var statements = handler.SelectMany(b => b.Statements).ToArray();
            var touched = statements.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable)
                .Concat(statements.OfType<ManagedCall>().Select(c => c.Result).OfType<LocalValue>().Select(l => l.Variable)).ToHashSet();
            return !touched.Contains(copy.Target.Variable) && !ManagedValues.Walk(copy.Value).OfType<LocalValue>().Any(l => touched.Contains(l.Variable));
        }

        private static bool Keep(List<ManagedCopy> real, ExitMatch match)
        {
            if (real.Count == 0) return true;
            if (match.Started) return false;
            match.Before.AddRange(real);
            return true;
        }

        private static bool Opposite(ManagedValue a, ManagedValue b) => (a, b) switch
        {
            (NegatedValue x, _) when ManagedStructure.Value(x.Operand, b) => true,
            (_, NegatedValue y) when ManagedStructure.Value(a, y.Operand) => true,
            (ComparisonValue { Condition: Cond.Eq } x, ComparisonValue { Condition: Cond.Ne } y) => ManagedStructure.Value(x.Left, y.Left) && ManagedStructure.Value(x.Right, y.Right),
            (ComparisonValue { Condition: Cond.Ne } x, ComparisonValue { Condition: Cond.Eq } y) => ManagedStructure.Value(x.Left, y.Left) && ManagedStructure.Value(x.Right, y.Right),
            _ => false,
        };

        private ManagedBody? Rewrite(ulong entry, IReadOnlyList<ulong> tryBlocks, Dictionary<ManagedEdge, ManagedEdge> exits)
        {
            var inTry = tryBlocks.ToHashSet();
            // 和新 try 重叠的区域要么包住它，要么连处理块一起嵌在里面：处理块在外面时，它回到 try 的边进不了 IL 的 try，异常的去向也变了。
            // 这个区域原来的处理块不再可达，不算在外面。
            var replaced = region.Handler.ToHashSet();
            bool Inside(ManagedRegion other) => other.Try.All(inTry.Contains) && other.Handler.All(a => inTry.Contains(a) || replaced.Contains(a));
            foreach (var other in body.Regions.Where(r => !ReferenceEquals(r, region)))
                if (other.Try.Any(inTry.Contains) && !tryBlocks.All(other.Try.Contains) && !Inside(other)
                    || other.Handler.Any(inTry.Contains) && !tryBlocks.All(other.Handler.Contains) && !Inside(other)) return null;
            var positions = body.Blocks.Select((b, i) => (b.Address, i)).ToDictionary(p => p.Address, p => p.i);
            var order = tryBlocks.Skip(1).OrderBy(a => positions[a]).Prepend(tryBlocks[0]).ToArray();
            var rewritten = new List<ManagedBlock>();
            var placed = false;
            foreach (var block in body.Blocks)
            {
                if (!inTry.Contains(block.Address)) { rewritten.Add(block); continue; }
                if (placed) continue;
                placed = true;
                rewritten.AddRange(order.Select(a => blocks[a] with
                {
                    Statements = blocks[a].Statements.Select(s => ManagedValues.MapEdges(s, e => exits.TryGetValue(e, out var exit) ? exit : e)).ToArray(),
                }));
                rewritten.AddRange(handler);
            }
            var added = handler.Select(b => b.Address).ToArray();
            var regions = body.Regions.Select(r => ReferenceEquals(r, region)
                ? new ManagedRegion(order, entry, added, null, ManagedRegionKind.Finally)
                : tryBlocks.All(r.Try.Contains) ? r with { Try = Ordered(r.Try, order, added) }
                : tryBlocks.All(r.Handler.Contains) ? r with { Handler = Ordered(r.Handler, order, added) }
                : r).ToArray();
            // 局部合并可能让几个 catch 共用保存异常的局部。出口路径上的值已经不写了，从 leave 的目标往后不能在重新赋值之前读它。
            var cleaned = Clean(body with { Blocks = rewritten, Regions = regions }, holders, destinations);
            return exits.Values.Select(e => e.Target).Distinct().Any(target => holders.Concat(renamed).Any(v => ReadBeforeWrite(cleaned, target, v))) ? null : cleaned;
        }

        /// <summary>外层区域的块序：新块放进去；这次调整了首块时，外层的第一个块不变。</summary>
        private static IReadOnlyList<ulong> Ordered(IReadOnlyList<ulong> outer, IReadOnlyList<ulong> order, IReadOnlyList<ulong> added) =>
            outer.Concat(order).Concat(added).Distinct().ToArray();
    }

    /// <summary>从 start 沿正常边走，variable 在被重新赋值之前是否被读取。</summary>
    private static bool ReadBeforeWrite(ManagedBody body, ulong start, Variable variable)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var visited = new HashSet<ulong>();
        var work = new Stack<ulong>();
        work.Push(start);
        while (work.TryPop(out var address))
        {
            if (!visited.Add(address) || !blocks.TryGetValue(address, out var block)) continue;
            var written = false;
            foreach (var statement in block.Statements)
            {
                var values = statement is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(statement);
                if (values.SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable.Equals(variable))) return true;
                if (statement is ManagedAssignment { Target: var target } && target.Variable.Equals(variable)) { written = true; break; }
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    if (edge.Copies.Any(c => ManagedValues.Walk(c.Value).OfType<LocalValue>().Any(l => l.Variable.Equals(variable)))) return true;
                    if (!edge.Copies.Any(c => c.Target.Variable.Equals(variable))) work.Push(edge.Target);
                }
            }
            if (written) continue;
        }
        return false;
    }

    /// <summary>删去不可达的块，和已经没有读取的异常局部、去向局部的赋值。</summary>
    private static ManagedBody Clean(ManagedBody body, HashSet<Variable> holders, HashSet<Variable> destinations)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var reached = new HashSet<ulong>();
        var work = new Stack<ulong>();
        void Visit(ulong address)
        {
            if (blocks.ContainsKey(address) && reached.Add(address)) work.Push(address);
        }
        Visit(body.Blocks[0].Address);
        for (var changed = true; changed;)
        {
            while (work.TryPop(out var address))
                foreach (var edge in blocks[address].Statements.SelectMany(ManagedValues.Edges)) Visit(edge.Target);
            changed = false;
            foreach (var region in body.Regions)
                if (region.Try.Any(reached.Contains) && !reached.Contains(region.HandlerEntry))
                {
                    Visit(region.HandlerEntry);
                    changed = true;
                }
        }
        var kept = body.Blocks.Where(b => reached.Contains(b.Address)).ToArray();
        for (var removed = true; removed;)
        {
            var read = kept.SelectMany(b => b.Statements).SelectMany(s => (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
            bool Dead(Variable variable) => (holders.Contains(variable) || destinations.Contains(variable)) && !read.Contains(variable);
            ManagedEdge Edge(ManagedEdge edge) => edge with { Copies = edge.Copies.Where(c => !Dead(c.Target.Variable)).ToArray() };
            bool Useless(ManagedStatement s) => s is ManagedAssignment { Target: var target } a && !read.Contains(target.Variable)
                && (a.ExceptionArrival && ManagedEffects.Statement(a).CanDiscard || a.Value is ConstantValue or LocalValue && Dead(target.Variable));
            removed = kept.SelectMany(b => b.Statements).Any(Useless);
            kept = kept.Select(b => b with
            {
                Statements = b.Statements.Where(s => !Useless(s)).Select(s => ManagedValues.MapEdges(s, Edge)).ToArray(),
            }).ToArray();
        }
        return body with
        {
            Blocks = kept,
            Regions = body.Regions.Where(r => r.Try.Any(reached.Contains)).Select(r => r with
            {
                Try = r.Try.Where(reached.Contains).ToArray(),
                Handler = r.Handler.Where(reached.Contains).ToArray(),
            }).ToArray(),
        };
    }
}
