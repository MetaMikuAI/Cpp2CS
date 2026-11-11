using System.Collections.Immutable;
using System.Diagnostics;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Tests;

internal static class QueryChecks
{
    public const string Command = "queries";
    private sealed class Chain(bool fail = false, long budget = long.MaxValue) : Query<int, int>(budget)
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            if (key == 0) return fail ? Outcome<int>.Failure(new("leaf", "底层失败")) : Outcome<int>.Success(0);
            var dependency = context.Get(this, key - 1);
            return dependency.IsSuccess ? Outcome<int>.Success(dependency.Value + 1) : dependency.Propagate<int>();
        }
    }
    private sealed class IdentityQuery : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key) => Outcome<int>.Success(key);
    }
    private sealed class Functional(IdentityQuery dependency) : Query<int, int>
    {
        private static int Read(QueryContext context, IdentityQuery query, int key) => context.Get(query, key).Value;
        public override Outcome<int> Compute(QueryContext context, int key) =>
            Outcome<int>.Success(Enumerable.Range(0, key).Select(i => Read(context, dependency, i)).Sum());
    }
    private sealed class CycleQuery : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key) => context.Get(this, 1 - key);
    }
    private sealed class Reach(bool first) : Query<int, int>
    {
        public Reach Other { get; set; } = null!;
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var other = context.Get(Other, key);
            return other.IsSuccess ? Outcome<int>.Success(other.Value | (first ? 1 : 2)) : other.Propagate<int>();
        }
    }
    private sealed class GraphReach : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var result = 1 << key;
            foreach (var next in context.Facts<GraphFacts>().Edges[key])
            {
                var value = context.Get(this, next);
                if (!value.IsSuccess) return value.Propagate<int>();
                result |= value.Value;
            }
            return Outcome<int>.Success(result);
        }
    }
    private sealed record GraphFacts(int[][] Edges);
    private sealed class Bridge : Query<int, int>
    {
        public Query<int, int> Dependency { get; set; } = null!;
        public override Outcome<int> Compute(QueryContext context, int key) => context.Get(Dependency, key);
    }
    private sealed class Routed : Query<int, int>
    {
        public Bridge Via { get; set; } = null!;
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            if (key != 0) return Outcome<int>.Success(1);
            var known = context.Get(this, 2);
            if (!known.IsSuccess) return known;
            var fresh = context.Get(Via, 1);
            return fresh.IsSuccess ? context.Get(Via, 2) : fresh;
        }
    }
    /// <summary>键 0 把键 1 的失败当作格的顶处理，再读取键 2；没有环。</summary>
    private sealed class Tolerant : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            if (key == 1) return Outcome<int>.Failure(new("member", "成员失败"));
            if (key == 2) return Outcome<int>.Success(4);
            var failed = context.Get(this, 1);
            var fine = context.Get(this, 2);
            return fine.IsSuccess ? Outcome<int>.Success((failed.IsSuccess ? failed.Value : 8) | fine.Value | 1) : fine.Propagate<int>();
        }
    }
    /// <summary>键 0 与键 1 成环，键 0 读过近似值之后失败。</summary>
    private sealed class FailingHead : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var other = context.Get(this, 1 - key);
            if (key == 0) return Outcome<int>.Failure(new("head", "环上的键失败"));
            return other.IsSuccess ? Outcome<int>.Success(other.Value | 2) : other.Propagate<int>();
        }
    }
    /// <summary>自环的组内查询，途中求一条组外的依赖链。</summary>
    private sealed class WithHelper(Chain helper) : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var self = context.Get(this, key);
            if (!self.IsSuccess) return self.Propagate<int>();
            var value = context.Get(helper, 3);
            return value.IsSuccess ? Outcome<int>.Success(self.Value | value.Value) : value.Propagate<int>();
        }
    }
    private sealed class Bits : ILattice<int>
    {
        public int Bottom => 0;
        public int Join(int left, int right) => left | right;
        public bool LessOrEqual(int left, int right) => (left | right) == right;
    }
    private sealed class BadJoin : ILattice<int>
    {
        public int Bottom => 0;
        public int Join(int left, int right) => 0;
        public bool LessOrEqual(int left, int right) => left <= right;
    }
    private sealed class Decreasing : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var previous = context.Get(this, key);
            return previous.IsSuccess ? Outcome<int>.Success(previous.Value == 0 ? 1 : 0) : previous;
        }
    }
    private sealed class DiscoveredLater : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var self = context.Get(this, key);
            if (!self.IsSuccess) return self;
            if (key == 1) return Outcome<int>.Success(2);
            if (self.Value == 0) return Outcome<int>.Success(1);
            var later = context.Get(this, 1);
            return later.IsSuccess ? Outcome<int>.Success(1 | later.Value) : later;
        }
    }
    private sealed class ThrowAtLeaf : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key) => key == 0
            ? throw new ArgumentException("作者错误") : context.Get(this, key - 1);
    }
    private sealed class Increasing : Query<int, int>
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            var previous = context.Get(this, key);
            return previous.IsSuccess ? Outcome<int>.Success(previous.Value + 1) : previous;
        }
    }
    private sealed class Numbers : ILattice<int>
    {
        public int Bottom => 0;
        public int Join(int left, int right) => Math.Max(left, right);
        public bool LessOrEqual(int left, int right) => left <= right;
    }
    private sealed class BudgetQuery(bool ignore = false) : Query<int, int>(3)
    {
        public override Outcome<int> Compute(QueryContext context, int key)
        {
            for (var i = 0; i < 4; i++)
                if (context.Step() is { } why && !ignore) return Outcome<int>.Failure(why);
            return Outcome<int>.Success(7);
        }
    }
    private sealed class Writes : Query<(BlockIdentity Block, Term Value), ImmutableArray<MemoryWrite>>
    {
        public override Outcome<ImmutableArray<MemoryWrite>> Compute(QueryContext context, (BlockIdentity Block, Term Value) key) =>
            Outcome<ImmutableArray<MemoryWrite>>.Success(context.Snapshot.Blocks.Single(b => b.Identity == key.Block)
                .Statements.OfType<MemoryWrite>().Where(s => s.Value == key.Value).ToImmutableArray());
    }
    private static NativeFunction Snapshot()
    {
        var terms = new TermTable();
        var id = new BlockIdentity();
        var address = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
        var builder = new FunctionBuilder(terms, id, 64, new(address));
        builder.Blocks.Add(new(id, [], [new MemoryWrite(new WriteIdentity(), address, 32, terms.Constant(7, 32))], new Return([])));
        return builder.Freeze();
    }
    private static bool Throws<T>(Action action) where T : Exception
    {
        try { action(); return false; }
        catch (T) { return true; }
    }
    public static int Run()
    {
        var a = new Assertions();
        var snapshot = Snapshot();
        a.True(!default(Outcome<int>).IsSuccess && default(Outcome<int>).Why is not null, "默认结果有失败原因");
        a.True(Outcome<int>.Success(0).Why is null && Outcome<int>.Success(0).Value == 0, "默认值可以是合法成功值");
        a.True(Throws<InvalidOperationException>(() => _ = default(Outcome<int>).Value), "失败不能读值");
        var query = new Chain();
        var context = new QueryContext(snapshot) { RecordDependencies = true };
        a.True(context.Get(query, 5).Value == 5 && context.Get(query, 5).Value == 5, "同键记忆");
        a.True(context.Statistics[query] == new QueryStatistics(6, 1, 0), "计算与命中统计");
        var second = new QueryContext(snapshot);
        a.True(second.Get(query, 3).Value == 3 && second.Get(query, 5).Value == 5, "请求顺序无关");
        a.True(second.Statistics[query].Computations == 6, "上下文缓存独立");
        a.True(context.Explain(query, 5).Dependencies.Single().Key.Equals(4), "依赖可追溯");
        a.True(Throws<InvalidOperationException>(() => second.Explain(query, 5)), "默认不记录依赖");
        var failure = new Chain(true);
        var failed = context.Get(failure, 2);
        a.True(failed.Why is { Code: "query.dependency", Cause: { Code: "query.dependency", Cause: { Code: "leaf", Cause: null } } }, "三层原因顺序");
        a.True(ReferenceEquals(context.Get(failure, 2).Why, failed.Why) && context.Statistics[failure] == new QueryStatistics(3, 1, 3), "失败记忆与统计");
        a.True(context.Get(new BudgetQuery(), 0).Why?.Code == "query.budget", "显式步数预算耗尽是洞");
        a.True(context.Get(new BudgetQuery(true), 0).Why?.Code == "query.budget", "忽略预算失败不能发布成功");
        a.True(context.Get(new Chain(budget: 0), 0).Value == 0, "无依赖计算不消耗步骤");
        a.True(context.Get(new Chain(budget: 0), 1).Why?.Code == "query.budget", "取依赖消耗一步");
        a.True(context.Get(new Chain(budget: 1), 5).Value == 5, "每次计算的预算独立");
        a.True(context.Get(new Functional(new()), 10).Value == 45, "lambda、LINQ 和辅助方法内同步取依赖");
        QueryCycleException? cycle = null;
        try { new QueryContext(snapshot).Get(new CycleQuery(), 0); }
        catch (QueryCycleException exception) { cycle = exception; }
        a.True(cycle?.Cycle.Select(x => (int)x.Key).SequenceEqual([0, 1, 0]) == true, "未声明环包含全部成员");
        var left = new Reach(true);
        var right = new Reach(false);
        left.Other = right; right.Other = left;
        FixedPointGroup Group(long limit) => new(limit,
            FixedPointMember.Create(left, _ => new Bits()), FixedPointMember.Create(right, _ => new Bits()));
        var fp = new QueryContext(snapshot, null, Group(100)) { RecordDependencies = true };
        var outside = new Bridge { Dependency = left };
        a.True(fp.Get(outside, 7).Value == 3 && fp.Get(right, 7).Value == 3, "两种查询动态键，组外只见收敛值");
        var reversed = new QueryContext(snapshot, null, Group(100));
        a.True(reversed.Get(right, 7).Value == 3 && reversed.Get(left, 7).Value == 3, "请求次序和记录模式不影响结果");
        var limited = new QueryContext(snapshot, null, Group(1));
        a.True(limited.Get(left, 7).Why is { Code: "query.fixed-point", Cause.Code: "query.fixed-point-limit" }, "组按依赖步数限制");
        a.True(!limited.Get(right, 7).IsSuccess, "失败组不发布部分结果");
        a.True(fp.Explain(left, 7).Dependencies.Length == 1, "多轮依赖去重");
        var bridgeA = new Bridge();
        var bridgeB = new Bridge();
        bridgeA.Dependency = bridgeB; bridgeB.Dependency = bridgeA;
        var bridgeGroup = new FixedPointGroup(100, FixedPointMember.Create(bridgeA, _ => new Bits()));
        a.True(Throws<QueryCycleException>(() => new QueryContext(snapshot, null, bridgeGroup).Get(bridgeA, 0)), "组外查询不能偷读近似值");
        var routed = new Routed();
        routed.Via = new Bridge { Dependency = routed };
        var routedContext = new QueryContext(snapshot, null,
            new FixedPointGroup(100, FixedPointMember.Create(routed, _ => new Bits())));
        a.True(routedContext.Get(routed, 0).Value == 1, "组外读取同组已完成键和独立求解其他键不构成环");
        var leafFailure = new Chain(true);
        var failedGroup = new QueryContext(snapshot, null, new FixedPointGroup(3, FixedPointMember.Create(leafFailure, _ => new Bits())));
        a.True(failedGroup.Get(leafFailure, 0).Why is { Code: "leaf" }, "成员失败就是它自己的原因");
        var tolerant = new Tolerant();
        QueryContext TolerantContext() => new(snapshot, null, new FixedPointGroup(100, FixedPointMember.Create(tolerant, _ => new Bits())));
        var tolerantForward = TolerantContext();
        a.True(tolerantForward.Get(tolerant, 0) is { IsSuccess: true, Value: 13 } && tolerantForward.Get(tolerant, 2).Value == 4
            && tolerantForward.Get(tolerant, 1).Why is { Code: "member" }, "一个键失败不波及同一次求解里的其他键");
        var tolerantBackward = TolerantContext();
        a.True(tolerantBackward.Get(tolerant, 2).Value == 4 && tolerantBackward.Get(tolerant, 1).Why is { Code: "member" }
            && tolerantBackward.Get(tolerant, 0) is { IsSuccess: true, Value: 13 }, "有失败的键时结果仍与请求次序无关");
        var head = new FailingHead();
        QueryContext HeadContext() => new(snapshot, null, new FixedPointGroup(100, FixedPointMember.Create(head, _ => new Bits())));
        var headForward = HeadContext();
        a.True(headForward.Get(head, 0).Why is { Code: "head" } && headForward.Get(head, 1).Why is { Code: "query.dependency", Cause.Code: "head" },
            "环上的键失败是格的顶，读过它近似值的键重算后看到失败");
        var headBackward = HeadContext();
        a.True(headBackward.Get(head, 1).Why is { Code: "query.dependency", Cause.Code: "head" } && headBackward.Get(head, 0).Why is { Code: "head" },
            "环上的失败与请求次序无关");
        var helper = new Chain();
        var withHelper = new WithHelper(helper);
        var exhausted = new QueryContext(snapshot, null, new FixedPointGroup(3, FixedPointMember.Create(withHelper, _ => new Bits())));
        a.True(exhausted.Get(withHelper, 0).Why is { Code: "query.fixed-point", Cause.Code: "query.fixed-point-limit" }
            && exhausted.Get(helper, 3) is { IsSuccess: true, Value: 3 }, "组的上限耗尽不污染组外查询的记忆");
        a.True(new QueryContext(snapshot, null, new FixedPointGroup(100, FixedPointMember.Create(withHelper, _ => new Bits())))
            .Get(withHelper, 0) is { IsSuccess: true, Value: 3 }, "上限充足时同一个查询收敛");
        var graph = new GraphFacts([[1], [2, 3], [0], [4], [3], []]);
        var reach = new GraphReach();
        var graphGroup = new FixedPointGroup(10_000, FixedPointMember.Create(reach, _ => new Bits()));
        var forward = new QueryContext(snapshot, graph, graphGroup);
        var backward = new QueryContext(snapshot, graph, graphGroup) { RecordDependencies = true };
        int Direct(int start)
        {
            var seen = new HashSet<int>();
            var todo = new Stack<int>(); todo.Push(start);
            while (todo.TryPop(out var node)) if (seen.Add(node)) foreach (var next in graph.Edges[node]) todo.Push(next);
            return seen.Aggregate(0, (bits, node) => bits | (1 << node));
        }
        foreach (var node in Enumerable.Range(0, 6)) a.True(forward.Get(reach, node).Value == Direct(node), "动态可达集合与直接计算一致");
        foreach (var node in Enumerable.Range(0, 6).Reverse()) a.True(backward.Get(reach, node).Value == Direct(node), "反向请求与直接计算一致");
        var bad = new IdentityQuery();
        a.True(Throws<InvalidOperationException>(() => new QueryContext(snapshot, null,
            new FixedPointGroup(100, FixedPointMember.Create(bad, _ => new BadJoin()))).Get(bad, 1)), "合并非上界被发现");
        var decreasing = new Decreasing();
        a.True(Throws<InvalidOperationException>(() => new QueryContext(snapshot, null,
            new FixedPointGroup(100, FixedPointMember.Create(decreasing, _ => new Bits()))).Get(decreasing, 0)), "已观察到的非单调结果被发现");
        var later = new DiscoveredLater();
        var laterContext = new QueryContext(snapshot, null,
            new FixedPointGroup(100, FixedPointMember.Create(later, _ => new Bits())));
        a.True(laterContext.Get(later, 0).Value == 3 && laterContext.Get(later, 1).Value == 2, "迭代过程中发现的新键加入参与者");
        var increasing = new Increasing();
        a.True(new QueryContext(snapshot, null, new FixedPointGroup(10, FixedPointMember.Create(increasing, _ => new Numbers())))
            .Get(increasing, 0).Why?.Cause?.Code == "query.fixed-point-limit", "无限高度格受步数上限保护");
        foreach (var depth in new[] { 100_000, 1_000_000 })
        {
            var deep = new QueryContext(snapshot);
            var timer = Stopwatch.StartNew();
            a.True(deep.Get(query, depth).Value == depth, "深链同步计算");
            a.True(deep.StackSwitches > 0, "确实切换栈");
            a.True(deep.Get(query, depth / 2).Value == depth / 2 && deep.Statistics[query] == new QueryStatistics(depth + 1, 1, 0), "换栈前后记忆与统计一致");
            Console.WriteLine($"查询深链：{depth} 层，换栈 {deep.StackSwitches} 次，{timer.Elapsed.TotalMilliseconds:F1} ms");
        }
        var deepFailure = new QueryContext(snapshot);
        a.True(!deepFailure.Get(failure, 100_000).IsSuccess && deepFailure.StackSwitches > 0 && deepFailure.Statistics[failure].Failures == 100_001, "换栈后的失败和统计");
        var throwing = new QueryContext(snapshot);
        a.True(Throws<ArgumentException>(() => throwing.Get(new ThrowAtLeaf(), 100_000)) && throwing.StackSwitches > 0,
            "换栈后的作者异常原样传回");
        var writes = new Writes();
        var key = (snapshot.Entry, snapshot.Terms.Constant(7, 32));
        a.True(context.Get(writes, key).Value.Length == 1 && context.Get(writes, key).Value == context.Get(writes, key).Value, "组合键的相等语义和记忆");
        Measure(a, snapshot);
        return a.Finish("查询框架");
    }
    private static void Measure(Assertions a, NativeFunction snapshot)
    {
        var identity = new IdentityQuery();
        var context = new QueryContext(snapshot);
        for (var i = 0; i < 100_000; i++) context.Get(identity, i);
        long sum = 0;
        var timer = new Stopwatch();
        var allocated = GC.GetAllocatedBytesForCurrentThread();
        timer.Start();
        for (var i = 0; i < 5_000_000; i++) sum += context.Get(identity, 42).Value;
        timer.Stop();
        var bytes = GC.GetAllocatedBytesForCurrentThread() - allocated;
        a.True(sum == 210_000_000 && bytes == 0, "命中零分配");
        Console.WriteLine($"查询性能：命中 {timer.Elapsed.TotalNanoseconds / 5_000_000:F1} ns/次，{bytes / 5_000_000.0:F1} B/次");
        // 隔离前面的百万层和映像检查留下的垃圾；扩容与本批次 GC 仍计入测量。
        var timings = new double[5];
        for (var sample = 0; sample < timings.Length; sample++)
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();
            GC.Collect();
            var cold = new QueryContext(snapshot);
            cold.Get(identity, -1);
            var gen0 = GC.CollectionCount(0);
            var gen1 = GC.CollectionCount(1);
            var gen2 = GC.CollectionCount(2);
            allocated = GC.GetAllocatedBytesForCurrentThread();
            timer.Restart();
            sum = 0;
            for (var i = 0; i < 100_000; i++) sum += cold.Get(identity, i).Value;
            timer.Stop();
            bytes = GC.GetAllocatedBytesForCurrentThread() - allocated;
            timings[sample] = timer.Elapsed.TotalNanoseconds / 100_000;
            a.True(sum == 4_999_950_000, "独立键计算结果");
            Console.WriteLine($"查询性能：无依赖计算 {timings[sample]:F1} ns/次，{bytes / 100_000.0:F1} B/次，GC={GC.CollectionCount(0) - gen0}/{GC.CollectionCount(1) - gen1}/{GC.CollectionCount(2) - gen2}（含存储与扩容）");
        }
        Array.Sort(timings);
        Console.WriteLine($"查询性能：无依赖计算中位数 {timings[2]:F1} ns/次");
    }
}
