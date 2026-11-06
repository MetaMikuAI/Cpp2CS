using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// clang 把相同的收尾合并成一个块，比如 a?.b ?? c 的失败路径。成功路径要跳过它到后面的合流：
/// if (a != null) { t = a.b; if (t != null) { x = t; goto L; } } x = c; L:
/// 两次判断之间隔着语句时，C# 的结构化控制流写不出这样的图，反编译器只能写 goto。
/// 每条路径执行一份收尾的副本，语义不变，if/else 就能表达，反编译器的 ?. 和 ?? 也才有机会匹配。
/// 判断之间没有语句时它能合并成 ||，循环的 continue 块它能认出 for，这两种不复制。
/// 入口是无条件跳转、条件分支的另一边也回到这个块时，是普通的 if (c) { S } 之后的合流，也不复制。
/// async 和迭代器的 MoveNext 不处理：反编译器要求恢复路径和完成路径共用一个块。
/// 收尾覆盖了刚判过空的局部时，那是 x = a?.b ?? c 被 clang 跳转穿透的结果：a 是空时直接接到 c，跳过了 x == null 的判断。
/// 这时不复制，把判断还原回去：空路径把 x 写成空，和非空路径在判断前合流。写成空的值马上被覆盖，语义不变。
/// </summary>
public static class JoinCopies
{
    /// <summary>新块的地址不对应原生代码，取高位以免与其他阶段的新块重合。</summary>
    private const ulong SyntheticAddress = 6UL << 60;
    private const int StatementLimit = 3;
    private const int PredecessorLimit = 6;
    private const int SearchLimit = 256;
    private const int BlockLimit = 4096;
    /// <summary>复制之后可能露出新的同类块。</summary>
    private const int Passes = 4;
    private const int FallbackLimit = 64;

    /// <param name="rewrites">还原和复制的次数，不含接起块。</param>
    public static ManagedBody Run(ManagedBody body, out int rewrites)
    {
        rewrites = 0;
        if (body.Method.Method.Name == "MoveNext" || body.Blocks.Count > BlockLimit) return body;
        var compacted = Compact(body);
        if (compacted is not null) body = compacted;
        for (var pass = 0; pass < FallbackLimit; pass++)
        {
            var next = Fallback(body);
            if (next is null) break;
            body = next;
            rewrites++;
        }
        for (var pass = 0; pass < Passes; pass++)
        {
            var next = Once(body);
            if (next is null) break;
            body = next;
            rewrites++;
        }
        return body;
    }

    /// <summary>调用把原生块切得很碎，收尾常常是一串只有一个入口的块。先接起来才看得出大小。</summary>
    private static ManagedBody? Compact(ManagedBody body)
    {
        var code = body.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        var counts = new Dictionary<ulong, int>();
        foreach (var edge in code.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges)) counts[edge.Target] = counts.GetValueOrDefault(edge.Target) + 1;
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        string Scope(ulong address) => string.Join(",", body.Regions.Select((r, i) => r.Try.Contains(address) ? $"t{i}" : r.Handler.Contains(address) ? $"h{i}" : ""));
        var changed = false;
        foreach (var address in body.Blocks.Select(b => b.Address))
        {
            if (!code.TryGetValue(address, out var statements)) continue;
            while (statements is [.., ManagedJump { Edge: { Copies.Count: 0 } edge }] && edge.Target != address && !entries.Contains(edge.Target)
                && counts.GetValueOrDefault(edge.Target) == 1 && code.ContainsKey(edge.Target) && Scope(edge.Target) == Scope(address))
            {
                statements.RemoveAt(statements.Count - 1);
                statements.AddRange(code[edge.Target]);
                code.Remove(edge.Target);
                changed = true;
            }
        }
        if (!changed) return null;
        return body with
        {
            Blocks = body.Blocks.Where(b => code.ContainsKey(b.Address)).Select(b => b with { Statements = code[b.Address] }).ToArray(),
            Regions = body.Regions.Select(r => r with { Try = r.Try.Where(code.ContainsKey).ToArray(), Handler = r.Handler.Where(code.ContainsKey).ToArray() }).ToArray(),
        };
    }

    /// <summary>判空的局部和空的一边。</summary>
    private static (LocalValue Local, ManagedEdge WhenNull)? NullTest(ManagedBranch branch) => branch.Condition switch
    {
        ComparisonValue { Condition: Cond.Eq, Left: LocalValue local, Right: ConstantValue { Bits: 0 } } when ManagedTypes.IsReferenceType(local.Type) => (local, branch.Taken),
        ComparisonValue { Condition: Cond.Ne, Left: LocalValue local, Right: ConstantValue { Bits: 0 } } when ManagedTypes.IsReferenceType(local.Type) => (local, branch.Fallthrough),
        _ => null,
    };

    /// <summary>块在读这个局部之前覆盖了它。</summary>
    private static bool Overwrites(ManagedBlock block, Variable variable)
    {
        bool Reads(ManagedValue value) => ManagedValues.Walk(value).Any(v => v is LocalValue local && local.Variable.Equals(variable));
        foreach (var statement in block.Statements)
        {
            var values = statement is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(statement);
            if (values.Any(Reads)) return false;
            if (statement is ManagedAssignment { Target: var target } && target.Variable.Equals(variable)) return true;
            if (statement is ManagedCall { Result: { } result } && result.Variable.Equals(variable)) return true;
            if (statement is ManagedJump { Edge.Copies: var copies })
                return copies.Any(c => c.Target.Variable.Equals(variable)) && !copies.Any(c => Reads(c.Value));
        }
        return false;
    }

    private static ManagedBody? Fallback(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = new Dictionary<ulong, List<Incoming>>();
        var switched = new HashSet<ulong>();
        foreach (var block in body.Blocks)
            foreach (var statement in block.Statements)
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    (incoming.TryGetValue(edge.Target, out var list) ? list : incoming[edge.Target] = []).Add(new(block.Address, edge));
                    if (statement is ManagedSwitch) switched.Add(edge.Target);
                }
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        string Scope(ulong address) => string.Join(",", body.Regions.Select((r, i) => r.Try.Contains(address) ? $"t{i}" : r.Handler.Contains(address) ? $"h{i}" : ""));
        foreach (var shared in body.Blocks)
        {
            if (entries.Contains(shared.Address) || switched.Contains(shared.Address) || !Small(shared) || !incoming.TryGetValue(shared.Address, out var edges) || edges.Count < 2) continue;
            var scope = Scope(shared.Address);
            if (edges.Any(e => Scope(e.From) != scope || e.Edge.Copies.Count != 0 || blocks[e.From].Statements[^1] is not ManagedBranch)) continue;
            foreach (var test in edges)
            {
                var branch = (ManagedBranch)blocks[test.From].Statements[^1];
                if (NullTest(branch) is not var (local, whenNull) || !ReferenceEquals(whenNull, test.Edge) || !Overwrites(shared, local.Variable)) continue;
                var address = SyntheticAddress | body.Blocks.Select(b => b.Address).Where(a => a >> 60 == SyntheticAddress >> 60).Select(a => ((a ^ SyntheticAddress) >> 40) + 1).DefaultIfEmpty(0UL).Max() << 40;
                var empty = new ManagedCopy(local, new ConstantValue(0, local.Type, local.Width));
                var others = edges.Where(e => e.From != test.From).Select(e => e.Edge).ToHashSet(ReferenceEqualityComparer.Instance);
                var rebuilt = new List<ManagedBlock>();
                foreach (var block in body.Blocks)
                {
                    if (block.Address == test.From)
                    {
                        rebuilt.Add(block with { Statements = [.. block.Statements.SkipLast(1), new ManagedJump(branch.Address, new ManagedEdge(address, []))] });
                        rebuilt.Add(new ManagedBlock(address, [branch]));
                        continue;
                    }
                    rebuilt.Add(block with { Statements = block.Statements.Select(s => ManagedValues.MapEdges(s, e => others.Contains(e) ? new ManagedEdge(address, [empty]) : e)).ToArray() });
                }
                IReadOnlyList<ulong> Extended(IReadOnlyList<ulong> members)
                {
                    if (!members.Contains(test.From)) return members;
                    var list = members.ToList();
                    list.Insert(list.IndexOf(test.From) + 1, address);
                    return list;
                }
                return body with { Blocks = rebuilt, Regions = body.Regions.Select(r => r with { Try = Extended(r.Try), Handler = Extended(r.Handler) }).ToArray() };
            }
        }
        return null;
    }

    private readonly record struct Incoming(ulong From, ManagedEdge Edge);

    private static ManagedBody? Once(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var incoming = new Dictionary<ulong, List<Incoming>>();
        var switched = new HashSet<ulong>();
        foreach (var block in body.Blocks)
            foreach (var statement in block.Statements)
                foreach (var edge in ManagedValues.Edges(statement))
                {
                    (incoming.TryGetValue(edge.Target, out var list) ? list : incoming[edge.Target] = []).Add(new(block.Address, edge));
                    if (statement is ManagedSwitch) switched.Add(edge.Target);
                }
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        string Scope(ulong address) => string.Join(",", body.Regions.Select((r, i) => r.Try.Contains(address) ? $"t{i}" : r.Handler.Contains(address) ? $"h{i}" : ""));

        var next = body.Blocks.Select(b => b.Address).Where(a => a >> 60 == SyntheticAddress >> 60).Select(a => ((a ^ SyntheticAddress) >> 40) + 1).DefaultIfEmpty(0UL).Max();
        var retargets = new Dictionary<ManagedEdge, ulong>(ReferenceEqualityComparer.Instance);
        var copies = new List<(ulong Address, ulong Origin, ulong After)>();
        foreach (var block in body.Blocks)
        {
            if (entries.Contains(block.Address) || switched.Contains(block.Address) || !Small(block)) continue;
            if (!incoming.TryGetValue(block.Address, out var all)) continue;
            var scope = Scope(block.Address);
            var edges = all.Where(e => Scope(e.From) == scope).ToArray();
            if (edges.Length != all.Count || edges.Length is < 2 or > PredecessorLimit) continue;
            if (block.Statements[^1] is ManagedJump { Edge.Target: var join })
            {
                // 没有路径跳过这个块时，它就是普通的合流，不需要复制。回到循环的块留给反编译器认 continue。
                if (incoming.GetValueOrDefault(join)?.Count is null or < 2 || Reaches(blocks, join, block.Address)) continue;
            }
            var conditional = edges.Where(e => blocks[e.From].Statements[^1] is ManagedBranch).ToArray();
            var skipping = conditional.Length >= 1 && conditional.Length < edges.Length && conditional.All(e => SkipsOver(blocks, e, block.Address));
            if (!skipping && (conditional.Length < 2 || !Separated(blocks, conditional, block.Address))) continue;
            foreach (var edge in skipping ? edges.Where(e => !conditional.Contains(e)).Skip(1).Concat(conditional) : conditional.Skip(1))
            {
                if (retargets.ContainsKey(edge.Edge)) continue;
                var address = SyntheticAddress | next++ << 40;
                retargets[edge.Edge] = address;
                copies.Add((address, block.Address, edge.From));
            }
        }
        if (copies.Count == 0) return null;
        ManagedStatement Retarget(ManagedStatement statement) => ManagedValues.MapEdges(statement, e => retargets.TryGetValue(e, out var target) ? e with { Target = target } : e);
        var after = copies.ToLookup(c => c.After);
        var rebuilt = new List<ManagedBlock>();
        foreach (var block in body.Blocks)
        {
            rebuilt.Add(block with { Statements = block.Statements.Select(Retarget).ToArray() });
            foreach (var copy in after[block.Address]) rebuilt.Add(new ManagedBlock(copy.Address, blocks[copy.Origin].Statements));
        }
        IReadOnlyList<ulong> Extended(IReadOnlyList<ulong> members)
        {
            var list = members.ToList();
            foreach (var copy in copies.Where(c => members.Contains(c.Origin))) list.Insert(list.IndexOf(copy.After) + 1, copy.Address);
            return list;
        }
        return body with { Blocks = rebuilt, Regions = body.Regions.Select(r => r with { Try = Extended(r.Try), Handler = Extended(r.Handler) }).ToArray() };
    }

    /// <summary>条件分支的另一边到不了这个块：它不是 if (c) { S } 的头，而是跳过这个块。</summary>
    private static bool SkipsOver(Dictionary<ulong, ManagedBlock> blocks, Incoming incoming, ulong shared) =>
        blocks[incoming.From].Statements[^1] is ManagedBranch branch && !Reaches(blocks, ReferenceEquals(branch.Taken, incoming.Edge) ? branch.Fallthrough.Target : branch.Taken.Target, shared);

    private static bool Small(ManagedBlock block) =>
        block.Statements.Count is > 0 and <= StatementLimit + 1 && block.Statements[^1] is ManagedJump or ManagedReturn or ManagedThrow
        && block.Statements.SkipLast(1).All(s => ManagedValues.Edges(s).Count == 0)
        // 委托的方法体会在反编译结果里展开成 lambda，复制一条语句等于复制整个方法体。
        && !block.Statements.SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).Any(v => v is DelegateValue or HoleValue);

    private static bool Reaches(Dictionary<ulong, ManagedBlock> blocks, ulong from, ulong target)
    {
        var visited = new HashSet<ulong>();
        var work = new Stack<ulong>();
        work.Push(from);
        while (work.TryPop(out var at) && visited.Count < SearchLimit)
        {
            if (at == target) return true;
            if (visited.Add(at) && blocks.TryGetValue(at, out var block))
                foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges)) work.Push(edge.Target);
        }
        // 搜索不完时当作回到循环，不复制。
        return work.Count > 0;
    }

    /// <summary>从一个入口走到另一个入口的路径上有语句：这两次判断不能合并成 ||。</summary>
    private static bool Separated(Dictionary<ulong, ManagedBlock> blocks, Incoming[] edges, ulong shared)
    {
        var sources = edges.Select(e => e.From).ToHashSet();
        foreach (var source in sources)
        {
            var visited = new HashSet<(ulong, bool)>();
            var work = new Stack<(ulong Block, bool Dirty)>();
            foreach (var edge in blocks[source].Statements.SelectMany(ManagedValues.Edges).Where(e => e.Target != shared)) work.Push((edge.Target, edge.Copies.Count > 0));
            while (work.TryPop(out var item) && visited.Count < SearchLimit)
            {
                if (!visited.Add(item) || !blocks.TryGetValue(item.Block, out var block)) continue;
                var dirty = item.Dirty || block.Statements.Count > 1;
                if (sources.Contains(item.Block) && item.Block != source && dirty) return true;
                foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges).Where(e => e.Target != shared)) work.Push((edge.Target, dirty || edge.Copies.Count > 0));
            }
        }
        return false;
    }
}
