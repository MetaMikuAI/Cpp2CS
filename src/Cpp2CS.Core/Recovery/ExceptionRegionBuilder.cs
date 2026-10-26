using Cpp2CS.Facts;
using Cpp2CS.Arm64;
using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed class ExceptionRegionPlan(ExceptionFragment entry, string kind)
{
    public ExceptionFragment Entry { get; } = entry;
    public string Kind { get; } = kind;
    public HashSet<ExceptionFragment> Try { get; } = [];
    public HashSet<ExceptionFragment> Handler { get; } = [];
    public ExceptionFragment? TryEntry { get; internal set; }
    public ExceptionRegionPlan? Parent { get; internal set; }
    public string? ParentPart { get; internal set; }
}
public sealed record ExceptionLayout(ExceptionStatementGraph Graph, string Reason, string Detail,
    ExceptionRegionPlan[] Regions, ExceptionFragment[] Order, ExceptionFragment[] Kept, ExceptionEntryPath[] EntryPaths, int[][] Edges)
{
    public bool Succeeded => Reason == "可排成";
}
/// <summary>被规范化的空桥及原始调用点；其 phi 来源仍在原始图，2b 必须处理，不能静默丢弃。</summary>
public sealed record ExceptionEntryPath(ExceptionFragment Source, ExceptionFragment[] Bridges, ExceptionFragment Entry);

/// <summary>
/// F5 2a 的区域构造，由 2b 的 MethodRecovery 消费成功见证。先按 action/SSA 证明 selector，再在语句图上
/// 做单入口闭包和严格包含检查；实际排列作为见证输出，2b 仍须 CIL/ILVerify。
/// </summary>
public static class ExceptionRegionBuilder
{
    public static ExceptionLayout Build(ProgramFacts facts, MachineFunction function) => Build(function, slot =>
        facts.Model.Image.ReadPointer(slot) is { } type && ExceptionFacts.TypeName(facts.Model.Image, type) == ExceptionFacts.WrapperName,
        address => function.Range.Contains(address) && facts.Code.Word(address) is { } word && A64.IsB(word) &&
            A64.Imm26Target(word, address) is var target && function.Range.Contains(target) ? target : null);
    internal static ExceptionLayout Build(MachineFunction function, Func<ulong, bool> wrapperSlot, Func<ulong, ulong?>? branchTarget = null) => new Builder(wrapperSlot, function, branchTarget).Run();

    private sealed class Builder(Func<ulong, bool> wrapperSlot, MachineFunction function, Func<ulong, ulong?>? branchTarget)
    {
        private readonly ExceptionStatementGraph graph = new(function, branchTarget);
        private readonly Dictionary<ExceptionFragment, ExceptionFragment[]> next = [];
        private readonly Dictionary<ExceptionFragment, List<ExceptionFragment>> previous = [];
        private readonly Dictionary<ExceptionFragment, ExceptionFragment[]> normal = [];
        private readonly Dictionary<ExceptionFragment, ExceptionFragment> exceptional = [];
        private readonly List<ExceptionEntryPath> entryPaths = [];
        private readonly Dictionary<Variable, long[]> selector = [];
        private readonly List<ExceptionRegionPlan> regions = [];
        private HashSet<ExceptionFragment> kept = [];

        private ExceptionLayout Result(string reason, string detail, ExceptionFragment[]? order = null) =>
            new(graph, reason, detail, regions.ToArray(), order ?? [], kept.OrderBy(f => f.Id).ToArray(), entryPaths.ToArray(),
                kept.OrderBy(f => f.Id).SelectMany(f => normal[f].Select(n => new[] { f.Id, n.Id, 0 })
                    .Concat(exceptional.TryGetValue(f, out var ex) ? [new[] { f.Id, ex.Id, 1 }] : [])).ToArray());
        private static HashSet<ExceptionFragment> Reach(IEnumerable<ExceptionFragment> roots, Func<ExceptionFragment, IEnumerable<ExceptionFragment>> edges)
        {
            var seen = new HashSet<ExceptionFragment>(); var pending = new Stack<ExceptionFragment>(roots);
            while (pending.TryPop(out var f)) if (seen.Add(f)) foreach (var n in edges(f)) pending.Push(n);
            return seen;
        }
        private static bool Bookkeeping(Call call) => call.Op?.Kind is OpKind.BeginCatch or OpKind.EndCatch;
        // InitClass、写屏障在现有 L3 已按运行时事实删除；其余未知调用不扩大受保护范围。
        private static bool NonThrowing(Stmt s) => s is Phi or Define or Store or Jump or Branch or Nop or Return ||
            s is Call { Op.Kind: OpKind.BeginCatch or OpKind.EndCatch or OpKind.InitClass or OpKind.WriteBarrier or OpKind.MemoryBarrier };
        // 取出异常对象、selector 或设置状态常量后汇合的落地块也是桥；常量与异常值经 φ 的异常边复制保留。
        // 异常从内层 catch 中传出时，落地块先 __cxa_end_catch（结束内层 catch）再转给外层的 selector 分派：同样是桥（CIL 退出内层 handler 是隐式的）。
        private static bool EmptyBridge(ExceptionFragment f) => f.Statements.All(s => s is Phi or Jump or Nop or Call { Op.Kind: OpKind.EndCatch }
            || s is Define { Value: Intrinsic { Name: "eh_exception" or "eh_selector" } or Const or Use or Ir.Convert { Operand: Use } });
        private ExceptionFragment Canonical(ExceptionFragment f)
        {
            var seen = new HashSet<ExceptionFragment>();
            while (seen.Add(f) && EmptyBridge(f) && normal[f] is [var n]) f = n;
            return f;
        }

        private long[]? Values(Expr e) => e switch
        {
            Use u => selector.GetValueOrDefault(u.Variable),
            Const c => [unchecked((long)c.Value)],
            Ir.Convert { Width: >= 32, Operand.Width: >= 32 } c => Values(c.Operand),
            _ => null,
        };

        private void Selectors()
        {
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToArray();
            Block Normalize(Block b)
            {
                var seen = new HashSet<Block>();
                while (seen.Add(b) && b.Handler is null && b.Statements.All(s => s is Phi or Jump or Nop
                    || s is Define { Target.Storage: { Bank: Bank.Gpr, Index: > 1 }, Value: Const })
                    && b.NormalSuccessors.ToArray() is [var n]) b = n;
                return b;
            }
            var byAddress = function.Blocks.GroupBy(b => b.Start).ToDictionary(g => g.Key, g => g.First());
            Block? Resolve(ulong address)
            {
                var seen = new HashSet<ulong>();
                while (!byAddress.ContainsKey(address) && seen.Add(address) && branchTarget?.Invoke(address) is { } target) address = target;
                return byAddress.GetValueOrDefault(address);
            }
            var incomingByPad = function.Range.ExceptionRegions.Where(r => r.LandingPad != 0).Select(r => (Region: r, Pad: Resolve(r.LandingPad)))
                .Where(p => p.Pad is not null).GroupBy(p => Normalize(p.Pad!)).ToDictionary(g => g.Key, g => g.Select(p => p.Region).ToArray());
            bool changed;
            do
            {
                changed = false;
                IEnumerable<ExceptionFragment> Successors(ExceptionFragment f)
                {
                    var successors = f.Normal.AsEnumerable();
                    if (f.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne } cmp } branch
                        && Values(cmp.Left) is { } left && Values(cmp.Right) is { } right)
                    {
                        var choices = left.SelectMany(l => right.Select(r => cmp.Cond == Cond.Eq ? l == r : l != r)).Distinct().ToArray();
                        if (choices is [var choice]) successors = successors.Where(n => n.Block.Start == (choice ? branch.Target : branch.Fallthrough));
                    }
                    if (f.Exceptional is { } ex && !f.Statements.OfType<Call>().All(Bookkeeping)) successors = successors.Append(ex);
                    return successors;
                }
                // 已证成的 selector 会切掉外语异常清理路径；其 phi 输入不能再阻塞外层 catch 的证明。
                var active = Reach([graph.Entry], Successors);
                var activeBlocks = active.Select(f => f.Block).ToHashSet();
                var normalEntries = active.SelectMany(f => Successors(f).Where(n => f.Normal.Contains(n)
                    && n.Block != f.Block && Normalize(n.Block) != Normalize(f.Block))).Select(n => Normalize(n.Block)).ToHashSet();
                foreach (var block in function.Blocks.Where(activeBlocks.Contains))
                foreach (var d in block.Statements.OfType<Define>().Where(d => d.Value is Intrinsic { Name: "eh_selector" }))
                {
                    if (selector.ContainsKey(d.Target)) continue;
                    if (normalEntries.Contains(Normalize(block)) || !incomingByPad.TryGetValue(Normalize(block), out var incoming)) continue;
                    var values = new HashSet<long>(); var proven = true;
                    foreach (var r in incoming)
                    {
                        var action = r.Actions.FirstOrDefault(a => a.Filter != 0);
                        if (action is null) values.Add(0);
                        else if (action.Filter > 0 && action.Kind == "catch-all") values.Add(action.Filter);
                        else if (action.Filter > 0 && action.TypeInfo is > 0 && wrapperSlot(action.TypeInfo.Value)) values.Add(action.Filter);
                        else proven = false;
                    }
                    if (proven) { selector[d.Target] = values.Order().ToArray(); changed = true; }
                }
                foreach (var d in definitions)
                    if (!selector.ContainsKey(d.Target) && Values(d.Value) is { } v) { selector[d.Target] = v; changed = true; }
                foreach (var block in function.Blocks.Where(activeBlocks.Contains))
                foreach (var p in block.Statements.OfType<Phi>())
                {
                    if (selector.ContainsKey(p.Target)) continue;
                    var inputs = p.Sources.Where((v, i) => v != p.Target && activeBlocks.Contains(block.Predecessors[i])).Distinct().ToArray();
                    if (inputs.Length > 0 && inputs.All(selector.ContainsKey))
                    { selector[p.Target] = inputs.SelectMany(v => selector[v]).Distinct().Order().ToArray(); changed = true; }
                }
            } while (changed);
        }

        public ExceptionLayout Run()
        {
            Selectors();
            foreach (var f in graph.Fragments)
            {
                var ns = f.Normal.ToArray();
                if (f.Statements.LastOrDefault() is Branch { Condition: Compare { Cond: Cond.Eq or Cond.Ne } cmp } branch &&
                    Values(cmp.Left) is { } left && Values(cmp.Right) is { } right)
                {
                    var choices = left.SelectMany(l => right.Select(r => cmp.Cond == Cond.Eq ? l == r : l != r)).Distinct().ToArray();
                    if (choices is [var choice]) ns = ns.Where(n => n.Block.Start == (choice ? branch.Target : branch.Fallthrough)).ToArray();
                }
                normal[f] = ns;
            }
            foreach (var f in graph.Fragments)
            {
                var ns = normal[f];
                var calls = f.Statements.OfType<Call>().ToArray();
                if (f.Exceptional is { } ex && !calls.All(Bookkeeping))
                {
                    var canonical = Canonical(ex);
                    exceptional[f] = canonical;
                    var bridges = new List<ExceptionFragment>(); var seen = new HashSet<ExceptionFragment>();
                    while (ex != canonical && seen.Add(ex)) { bridges.Add(ex); ex = normal[ex].Single(); }
                    entryPaths.Add(new(f, bridges.ToArray(), canonical));
                    next[f] = [.. ns, canonical];
                }
                else next[f] = ns;
                previous[f] = [];
            }
            kept = Reach([graph.Entry], f => next[f]);
            if (kept.FirstOrDefault(f => f.MissingLandingPad is not null && !f.Statements.OfType<Call>().All(Bookkeeping)) is { } missing)
                return Result("未证成/L2已删除落地块", $"{missing} site=0x{missing.NativeExceptionSite:x} pad=0x{missing.MissingLandingPad:x}");
            foreach (var f in kept) foreach (var n in next[f].Where(kept.Contains)) previous[n].Add(f);
            if (!kept.Any(exceptional.ContainsKey))
                return Result("未证成/L2无异常边", "LSDA 存在但 L2 已无活动异常边");
            var byEntry = new Dictionary<ExceptionFragment, ExceptionRegionPlan>();
            foreach (var source in kept.Where(exceptional.ContainsKey))
            {
                var pad = exceptional[source];
                if (!byEntry.TryGetValue(pad, out var region))
                {
                    var body = Handler(pad);
                    if (body.Error is { } error) return Result(error, pad.ToString());
                    if (body.Kind == "bookkeeping") continue;
                    region = new(pad, body.Kind); region.Handler.UnionWith(body.Blocks);
                    byEntry.Add(pad, region); regions.Add(region);
                }
                region.Try.Add(source);
            }
            if (regions.Count == 0) return Result("未证成/只有清理", "无 catch/fault 区域");
            var protectedBy = regions.SelectMany(r => r.Try.Select(f => (Fragment: f, Region: r))).ToDictionary(p => p.Fragment, p => p.Region);
            bool CanContain(ExceptionRegionPlan inner, ExceptionRegionPlan outer) => inner != outer && inner.Handler.All(f =>
                f.Statements.All(NonThrowing) || protectedBy.GetValueOrDefault(f) == outer);
            // 普通后继的共同支配者补齐每个 try；支配图含异常边，支持 try/catch 内的完整嵌套。
            var dom = Dominators();
            HashSet<ExceptionFragment>? TryClosure(ExceptionRegionPlan region)
            {
                var head = region.Try.First();
                while (!region.Try.All(f => Dominates(dom, head, f)))
                {
                    if (dom[head] == head) return null;
                    head = dom[head];
                }
                var closure = Reach(region.Try, f => f == head ? [] : previous[f].Where(p => normal[p].Contains(f)));
                closure.Add(head);
                // 连接语句即使可能抛出（原生侧没有指向本 handler 的异常边）也并入 try：不做静态证明，由执行对照判定（用户决定）。
                return closure;
            }
            foreach (var region in regions)
            {
                if (TryClosure(region) is not { } closure) return Result("未证成/无共同入口", region.Entry.ToString());
                region.Try.UnionWith(closure);
            }
            // 若外层 try 已包含内层的一部分，就只能完整包含内层 try+handler。不得只包含 handler。
            bool expanded;
            do
            {
                expanded = false;
                foreach (var outer in regions)
                    foreach (var inner in regions.Where(r => r != outer))
                    {
                        // catch 体抛出的异常由外层接住时，外层 try 包含整个内层 try 语句（C# 的 try 按词法嵌套；原生侧内层 try 的语句只指向内层 handler）。
                        if (outer.Try.Overlaps(inner.Handler) && !inner.Try.Contains(outer.Entry) && !inner.Handler.Contains(outer.Entry))
                            foreach (var f in inner.Try) expanded |= outer.Try.Add(f);
                        if (!outer.Try.Overlaps(inner.Try) || inner.Try.IsSupersetOf(outer.Try)) continue;
                        if (!inner.Try.IsSubsetOf(outer.Try))
                        {
                            if (Environment.GetEnvironmentVariable("CPP2CS_EH_DEBUG") == "1")
                                foreach (var r in new[] { outer, inner })
                                    Console.Error.WriteLine($"  [EH] {r.Kind} entry={r.Entry} try=[{string.Join(" ", r.Try.OrderBy(x => x.Id))}] handler=[{string.Join(" ", r.Handler.OrderBy(x => x.Id))}]");
                            return Result("未证成/try交叉", $"{outer.Entry}/{inner.Entry}");
                        }
                        if (!CanContain(inner, outer)) return Result("未证成/内层handler抛出目标不同", $"{outer.Entry}/{inner.Entry}");
                        foreach (var f in inner.Handler) expanded |= outer.Try.Add(f);
                    }
                // 并入内层区域后，原共同入口可能已不再支配所有成员，需要补齐新增路径。
                foreach (var region in regions)
                {
                    if (TryClosure(region) is not { } closure) return Result("未证成/无共同入口", region.Entry.ToString());
                    foreach (var f in closure) expanded |= region.Try.Add(f);
                }
            } while (expanded);
            // catch 与正常路径共用的尾部（C++ 编译器合并了相同代码）移出 handler，handler 以 leave 跳到共用尾部；启发式，由执行对照判定（用户决定）。
            foreach (var region in regions.Where(r => r.Kind == "catch"))
                while (region.Handler.Where(f => f != region.Entry && previous[f].Any(p => !region.Handler.Contains(p) && normal[p].Contains(f))).ToArray() is { Length: > 0 } shared)
                {
                    region.Handler.ExceptWith(shared);
                    region.Handler.IntersectWith(Reach([region.Entry], f => normal[f].Where(region.Handler.Contains)));
                }
            foreach (var region in regions)
            {
                if (region.Try.Overlaps(region.Handler)) return Result("未证成/try与自身handler交叉", region.Entry.ToString());
                var heads = region.Try.Where(f => f == graph.Entry || previous[f].Any(p => !region.Try.Contains(p))).ToArray();
                if (heads.Length != 1) return Result("未证成/多入口try", $"{region.Entry}: {heads.Length}");
                region.TryEntry = heads[0];
                foreach (var f in region.Handler)
                    if (previous[f].Any(p => !region.Handler.Contains(p) && normal[p].Contains(f)))
                    {
                        if (Environment.GetEnvironmentVariable("CPP2CS_EH_DEBUG") == "1")
                            Console.Error.WriteLine($"  [EH] {region.Kind} entry={region.Entry} f={f} handler=[{string.Join(" ", region.Handler.OrderBy(x => x.Id))}] try=[{string.Join(" ", region.Try.OrderBy(x => x.Id))}] outside=[{string.Join(" ", previous[f].Where(p => !region.Handler.Contains(p) && normal[p].Contains(f)).Select(p => $"{p}: {string.Join("; ", p.Statements)} ← {string.Join(",", previous[p])}"))}]");
                        return Result("未证成/handler正常外入边", f.ToString());
                    }
            }
            foreach (var a in regions)
                foreach (var b in regions.Where(r => r != a))
                {
                    var allA = a.Try.Concat(a.Handler).ToHashSet();
                    var allB = b.Try.Concat(b.Handler).ToHashSet();
                    if (!allA.Overlaps(allB)) continue;
                    if (allA.IsSubsetOf(b.Try) || allA.IsSubsetOf(b.Handler))
                    {
                        if (a.Parent is null || allB.Count < a.Parent.Try.Count + a.Parent.Handler.Count)
                        { a.Parent = b; a.ParentPart = allA.IsSubsetOf(b.Try) ? "try" : "handler"; }
                    }
                    else if (!allB.IsSubsetOf(a.Try) && !allB.IsSubsetOf(a.Handler))
                    {
                        if (Environment.GetEnvironmentVariable("CPP2CS_EH_DEBUG") == "1")
                            foreach (var r in new[] { a, b })
                                Console.Error.WriteLine($"  [EH] {r.Kind} entry={r.Entry} try=[{string.Join(" ", r.Try.OrderBy(x => x.Id))}] handler=[{string.Join(" ", r.Handler.OrderBy(x => x.Id))}]");
                        return Result("未证成/区域交叉或共享handler", $"{a.Entry}/{b.Entry}");
                    }
                }
            var order = new List<ExceptionFragment>();
            void Emit(HashSet<ExceptionFragment> members, ExceptionRegionPlan? parent, string? part, ExceptionFragment entry)
            {
                var children = regions.Where(r => r.Parent == parent && r.ParentPart == part).ToArray();
                var assigned = children.SelectMany(r => r.Try.Concat(r.Handler)).ToHashSet();
                var units = members.Except(assigned).Select(f => (Head: f, Child: (ExceptionRegionPlan?)null))
                    .Concat(children.Select(r => (Head: r.TryEntry!, Child: (ExceptionRegionPlan?)r)))
                    .OrderBy(p => p.Head == entry || p.Child is { } r && r.Try.Contains(entry) ? 0 : 1).ThenBy(p => p.Head.Id);
                foreach (var unit in units)
                    if (unit.Child is { } child) { Emit(child.Try, child, "try", child.TryEntry!); Emit(child.Handler, child, "handler", child.Entry); }
                    else order.Add(unit.Head);
            }
            Emit(kept, null, null, graph.Entry);
            if (order.Count != kept.Count || order.Distinct().Count() != kept.Count) return Result("未证成/排列重复或丢失", "区域树覆盖不完整");
            foreach (var region in regions)
            {
                foreach (var set in new[] { region.Try, region.Handler })
                {
                    var positions = set.Select(f => order.IndexOf(f)).ToArray();
                    if (positions.Max() - positions.Min() + 1 != positions.Length) return Result("未证成/区间不连续", region.Entry.ToString());
                }
                if (order.IndexOf(region.TryEntry!) != region.Try.Min(order.IndexOf) || order.IndexOf(region.Entry) != region.Handler.Min(order.IndexOf) ||
                    region.Try.Max(order.IndexOf) + 1 != region.Handler.Min(order.IndexOf)) return Result("未证成/入口或相邻排列", region.Entry.ToString());
            }
            return Result("可排成", $"{regions.Count} 个区域；语句图严格嵌套，尚未写出 CIL", order.ToArray());
        }

        private (string Kind, HashSet<ExceptionFragment> Blocks, string? Error) Handler(ExceptionFragment entry)
        {
            var body = new HashSet<ExceptionFragment>();
            var states = new Dictionary<ExceptionFragment, bool>();
            var pending = new Stack<(ExceptionFragment Fragment, bool Catching)>(); pending.Push((entry, false));
            var begins = new HashSet<Call>(); var stops = 0; var resume = false; var outsideThrow = false;
            while (pending.TryPop(out var state))
            {
                var (f, catching) = state;
                if (states.TryGetValue(f, out var oldState))
                {
                    if (oldState != catching) return ("", body, "未证成/捕获状态在汇合处不同");
                    continue;
                }
                states[f] = catching; body.Add(f);
                var stop = false;
                foreach (var call in f.Statements.OfType<Call>())
                {
                    if (call.Op?.Kind == OpKind.BeginCatch)
                    {
                        if (catching) return ("", body, "未证成/共享前导多重BeginCatch");
                        begins.Add(call); catching = true;
                    }
                    if (call.Op?.Kind == OpKind.EndCatch && catching)
                    { stop = true; stops++; }
                    if (call.Op?.Kind is OpKind.ThrowManaged or OpKind.Rethrow or OpKind.Throw or OpKind.ThrowNew)
                    { stop = true; stops++; outsideThrow |= !catching; }
                    if (call.Op?.Kind == OpKind.ResumeUnwind) { stop = true; resume = true; stops++; }
                    if (call.Op?.Kind == OpKind.Terminate) return ("", body, "未证成/可达Terminate或selector来源");
                }
                if (stop) continue;
                if (normal[f].Length == 0) return ("", body, "未证成/handler出口未识别");
                foreach (var n in normal[f]) pending.Push((n, catching));
            }
            if (begins.Count == 1 && stops > 0 && !resume && !outsideThrow) return ("catch", body, null);
            if (begins.Count > 1) return ("", body, "未证成/共享前导多重BeginCatch");
            if (begins.Count > 0) return ("", body, "未证成/selector来源未证成");
            if (!resume) return ("", body, "未证成/无BeginCatch的前导");
            var pure = body.SelectMany(f => f.Statements).All(s => s is Phi or Jump or Nop ||
                s is Define { Value: Intrinsic { Name: "eh_exception" or "eh_selector" } } ||
                s is Call { Op.Kind: OpKind.EndCatch or OpKind.ResumeUnwind });
            return (pure ? "bookkeeping" : "fault", body, null);
        }

        private Dictionary<ExceptionFragment, ExceptionFragment> Dominators()
        {
            var post = new List<ExceptionFragment>(); var seen = new HashSet<ExceptionFragment>();
            var stack = new Stack<(ExceptionFragment Node, bool Exit)>(); stack.Push((graph.Entry, false));
            while (stack.TryPop(out var item))
                if (item.Exit) post.Add(item.Node);
                else if (seen.Add(item.Node)) { stack.Push((item.Node, true)); foreach (var n in next[item.Node]) stack.Push((n, false)); }
            post.Reverse(); var index = post.Select((f, i) => (f, i)).ToDictionary(p => p.f, p => p.i);
            var dom = new Dictionary<ExceptionFragment, ExceptionFragment> { [graph.Entry] = graph.Entry };
            ExceptionFragment Meet(ExceptionFragment a, ExceptionFragment b)
            {
                while (a != b) { while (index[a] > index[b]) a = dom[a]; while (index[b] > index[a]) b = dom[b]; }
                return a;
            }
            bool changed;
            do
            {
                changed = false;
                foreach (var f in post.Skip(1))
                {
                    var candidates = previous[f].Where(dom.ContainsKey).ToArray();
                    if (candidates.Length == 0) continue;
                    var parent = candidates.Aggregate(Meet);
                    if (dom.GetValueOrDefault(f) != parent) { dom[f] = parent; changed = true; }
                }
            } while (changed);
            return dom;
        }
        private static bool Dominates(Dictionary<ExceptionFragment, ExceptionFragment> dom, ExceptionFragment a, ExceptionFragment b)
        {
            while (b != a && dom[b] != b) b = dom[b];
            return a == b;
        }
    }
}
