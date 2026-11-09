using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 两臂都以同一个被内联方法开头时，clang 把方法开头不依赖分支的一段（如 List.Add 的 _version++ 与 _items、_size 的读取）
/// 提到调用方分支之前，各臂只剩方法的其余部分，每个内联区域都被分支切开。
/// 分支条件只由局部、实参与常量组成、不读这段赋值的局部时，这段在分支前后执行结果相同：复制到两臂开头、从原处删去，
/// 各臂重新是完整的内联形态。只作用于含待证访问（只能来自被内联方法）的这一段。
/// </summary>
internal sealed partial class TemplateRecovery
{
    /// <summary>
    /// 把可以下沉的前缀复制到两臂，直到没有可下沉的前缀；一个也没有时为 null。两份前缀赋值的局部各换成新局部（从 next 起编号），
    /// 并在各臂独占可达的块中改名：前缀的局部只在前缀中赋值、只在某一臂独占可达的块中使用时才下沉，否则合流后的使用分不清来自哪一份。
    /// </summary>
    private static ManagedBody? SinkHoistedPrefixes(ManagedBody body, ref int next)
    {
        // 臂里还可以有被提前的前缀（嵌套的分支）：每轮在新方法体上重新找，一轮里互不重叠。
        ManagedBody? sunk = null;
        for (var round = 0; round < 64 && SinkOnce(sunk ?? body, ref next) is { } further; round++) sunk = further;
        return sunk;
    }

    private static ManagedBody? SinkOnce(ManagedBody body, ref int next)
    {
        var entry = body.Blocks.Count > 0 ? body.Blocks[0].Address : 0;
        var successors = body.Blocks.ToDictionary(b => b.Address, b => b.Statements.SelectMany(Targets).Distinct().ToArray());
        var predecessors = new Dictionary<ulong, int>();
        foreach (var target in body.Blocks.SelectMany(b => b.Statements).SelectMany(Targets))
            predecessors[target] = predecessors.GetValueOrDefault(target) + 1;
        var assignments = new Dictionary<Variable, int>();
        foreach (var variable in body.Blocks.SelectMany(b => b.Statements).SelectMany(Assigned).Concat(body.Regions.Select(r => r.Exception?.Variable).OfType<Variable>()))
            assignments[variable] = assignments.GetValueOrDefault(variable) + 1;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var idom = ImmediateDominators(body.Blocks[0].Address, successors);
        // 被臂的入口支配的块：入口只有这一个前驱，到达这些块都经过这一臂。
        HashSet<ulong> Dominated(ulong head) => body.Blocks.Select(b => b.Address).Where(address =>
        {
            for (var at = address; idom.TryGetValue(at, out var up); at = up)
            {
                if (at == head) return true;
                if (up == at) return false;
            }
            return false;
        }).ToHashSet();
        var replaced = new Dictionary<ulong, IReadOnlyList<ManagedStatement>>();
        var renames = new Dictionary<ulong, Dictionary<Variable, LocalValue>>();
        var used = new HashSet<ulong>();
        foreach (var block in body.Blocks)
        {
            if (block.Statements is not [.., ManagedBranch { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } branch]
                || branch.Taken.Target == branch.Fallthrough.Target
                || new[] { branch.Taken.Target, branch.Fallthrough.Target }.Any(t => t == entry || !blocks.ContainsKey(t) || predecessors.GetValueOrDefault(t) != 1
                    || !SameRegions(body, block.Address, t) || used.Contains(t))
                || used.Contains(block.Address) || !LocalCondition(branch.Condition)) continue;
            var read = ConditionRoots(branch.Condition);
            var start = block.Statements.Count - 1;
            while (start > 0 && block.Statements[start - 1] is ManagedAssignment or ManagedStore && HasPending(block.Statements[start - 1])
                && !(WrittenRoot(block.Statements[start - 1]) is { } written && read.Contains(written)))
                start--;
            var end = block.Statements.Count - 1;
            var (onlyTaken, onlyFallthrough) = (Dominated(branch.Taken.Target), Dominated(branch.Fallthrough.Target));
            // 前缀的局部只在前缀中赋值，前缀之外读它们的块都被某一臂的入口支配；不成立时从前面去掉语句再试
            // （前缀的前部可能是更早下沉进来、合流后仍要用的另一段）。
            ManagedStatement[] prefix = [];
            LocalValue[] locals = [];
            for (; start < end; start++)
            {
                prefix = block.Statements.Skip(start).Take(end - start).ToArray();
                locals = prefix.OfType<ManagedAssignment>().Select(a => a.Target).ToArray();
                var variables = locals.Select(l => l.Variable).ToHashSet();
                var candidate = prefix;
                if (locals.All(l => assignments.GetValueOrDefault(l.Variable) == 1)
                    && !body.Blocks.Any(b => !onlyTaken.Contains(b.Address) && !onlyFallthrough.Contains(b.Address)
                        && b.Statements.Where(st => !candidate.Any(p => ReferenceEquals(p, st))).Any(st => Reads(st).Any(variables.Contains)))) break;
            }
            if (start == end) continue;
            used.UnionWith([block.Address, .. onlyTaken, .. onlyFallthrough]);
            replaced[block.Address] = [.. block.Statements.Take(start), branch];
            foreach (var arm in new[] { onlyTaken, onlyFallthrough })
            {
                var map = new Dictionary<Variable, LocalValue>();
                foreach (var local in locals) map[local.Variable] = new LocalValue(new Variable(Storage.Temp(1000 + next++), 1), local.Type, local.Width);
                foreach (var address in arm) renames[address] = map;
                var head = arm == onlyTaken ? branch.Taken.Target : branch.Fallthrough.Target;
                replaced[head] = [.. prefix.Select(st => Rename(st, map)), .. blocks[head].Statements.Select(st => Rename(st, map))];
            }
        }
        if (replaced.Count == 0) return null;
        return body with
        {
            Blocks = body.Blocks.Select(b => replaced.TryGetValue(b.Address, out var statements) ? b with { Statements = statements }
                : renames.TryGetValue(b.Address, out var map) ? b with { Statements = b.Statements.Select(st => Rename(st, map)).ToArray() } : b).ToArray(),
        };
    }

    /// <summary>语句赋值的局部：赋值、调用与 await 的结果、边上并行复制的目标。</summary>
    private static IEnumerable<Variable> Assigned(ManagedStatement statement) => (statement switch
    {
        ManagedAssignment a => [a.Target.Variable],
        ManagedCall { Result: { } result } => [result.Variable],
        ManagedAwait { Result: { } result } => [result.Variable],
        _ => Array.Empty<Variable>(),
    }).Concat(ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => c.Target.Variable));

    private static IEnumerable<Variable> Reads(ManagedStatement statement) =>
        ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable);

    /// <summary>把语句中的局部按 map 改名（含赋值目标），每次得到新的语句对象。</summary>
    private static ManagedStatement Rename(ManagedStatement statement, IReadOnlyDictionary<Variable, LocalValue> map)
    {
        ManagedValue Value(ManagedValue value) => value is LocalValue local && map.TryGetValue(local.Variable, out var renamed) ? renamed : ManagedValues.Map(value, Value);
        var mapped = ManagedValues.Map(statement, Value);
        mapped = mapped is ManagedAssignment assignment && map.TryGetValue(assignment.Target.Variable, out var target) ? assignment with { Target = target } : mapped;
        return ReferenceEquals(mapped, statement) ? statement with { } : mapped;
    }

    /// <summary>从 entry 起的直接支配者（Cooper、Harvey、Kennedy 的迭代算法）；入口的直接支配者是自身，不可达的块不在其中。</summary>
    private static Dictionary<ulong, ulong> ImmediateDominators(ulong entry, IReadOnlyDictionary<ulong, ulong[]> successors)
    {
        var order = new List<ulong>();
        var seen = new HashSet<ulong> { entry };
        var stack = new Stack<(ulong Block, int Next)>([(entry, 0)]);
        while (stack.TryPop(out var top))
        {
            var next = successors.GetValueOrDefault(top.Block) ?? [];
            if (top.Next < next.Length)
            {
                stack.Push((top.Block, top.Next + 1));
                if (seen.Add(next[top.Next])) stack.Push((next[top.Next], 0));
            }
            else order.Add(top.Block);
        }
        order.Reverse();
        var rank = order.Select((b, i) => (b, i)).ToDictionary(p => p.b, p => p.i);
        var predecessors = order.ToDictionary(b => b, _ => new List<ulong>());
        foreach (var block in order)
            foreach (var successor in successors.GetValueOrDefault(block) ?? [])
                if (predecessors.TryGetValue(successor, out var list)) list.Add(block);
        var idom = new Dictionary<ulong, ulong> { [entry] = entry };
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var block in order.Skip(1))
            {
                ulong? chosen = null;
                foreach (var predecessor in predecessors[block].Where(idom.ContainsKey))
                {
                    if (chosen is not { } current) { chosen = predecessor; continue; }
                    var (a, b) = (predecessor, current);
                    while (a != b)
                    {
                        while (rank[a] > rank[b]) a = idom[a];
                        while (rank[b] > rank[a]) b = idom[b];
                    }
                    chosen = a;
                }
                if (chosen is { } found && (!idom.TryGetValue(block, out var old) || old != found)) { idom[block] = found; changed = true; }
            }
        }
        return idom;
    }

    private static IEnumerable<ulong> Targets(ManagedStatement statement) => statement switch
    {
        ManagedJump jump => [jump.Edge.Target],
        ManagedBranch branch => [branch.Taken.Target, branch.Fallthrough.Target],
        ManagedSwitch table => table.Cases.Select(c => c.Target),
        _ => [],
    };

    /// <summary>两块属于相同的异常区域（try 与处理块）：语句在它们之间移动不改变所受的保护。</summary>
    private static bool SameRegions(ManagedBody body, ulong a, ulong b) =>
        body.Regions.All(r => r.Try.Contains(a) == r.Try.Contains(b) && r.Handler.Contains(a) == r.Handler.Contains(b));

    /// <summary>
    /// 条件只由局部、实参、常量、按值的结构体局部或实参的字段，以及不读内存、不抛出的运算组成：
    /// 求值不抛出，也不读对象或数组的存储（前缀的写入改不到它）。
    /// </summary>
    private static bool LocalCondition(ManagedValue condition) => ManagedValues.Walk(condition).All(v => v is LocalValue or ArgumentValue or ConstantValue
        or ComparisonValue or BooleanValue or NegatedValue or ConversionValue or UnaryValue
        or BinaryValue { Op: not (BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem) }
        || v is FieldValue { Pending: null, Accessor: null } field && ValueRoot(field));

    /// <summary>字段链的根是按值的结构体局部或实参（不是引用、指针或托管指针）。</summary>
    private static bool ValueRoot(FieldValue field) => field.Receiver switch
    {
        FieldValue inner => inner.Pending is null && inner.Accessor is null && ValueRoot(inner),
        LocalValue or ArgumentValue => !ManagedTypes.IsReferenceType(field.Receiver.Type) && field.Receiver.Type is not (ByRefRef or PointerRef or GenericParameterRef),
        _ => false,
    };

    /// <summary>条件读的局部与实参（含字段链的根）。</summary>
    private static HashSet<object> ConditionRoots(ManagedValue condition) =>
        ManagedValues.Walk(condition).Select(v => v switch { LocalValue l => (object)l.Variable, ArgumentValue a => a.Index, _ => null }).OfType<object>().ToHashSet();

    /// <summary>语句写到的局部或实参：赋值目标，或写入目标字段链的根。</summary>
    private static object? WrittenRoot(ManagedStatement statement) => statement switch
    {
        ManagedAssignment a => a.Target.Variable,
        ManagedStore { Target: var target } => WriteRoot(target),
        _ => null,
    };

    private static object? WriteRoot(ManagedValue value) => value switch
    {
        FieldValue field => WriteRoot(field.Receiver),
        AddressValue address => WriteRoot(address.Target),
        LocalValue local => local.Variable,
        ArgumentValue argument => argument.Index,
        _ => null,
    };

    private static bool HasPending(ManagedStatement statement) =>
        ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).Any(v => PendingOf(v) is not null);
}
