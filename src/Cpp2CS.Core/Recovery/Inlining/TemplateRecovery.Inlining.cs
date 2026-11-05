using Cpp2CS.Recovery.Effects;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>
/// 多语句内联的逆。调用方中对不可访问字段的访问必然来自被内联的方法体；字段所在类型中访问该字段、方法体无环的实例方法是候选，
/// 以它自身的恢复体为模板，在调用方从某一语句起两边同步做符号执行：
/// 读取按路径上已知的写入归一（不同字段不相干，调用之后分代），赋值与跳转只改变环境；
/// 两边沿相同（或取反）的分支走过每条路径，写入、调用、检查与抛出逐一对应，形参在首次出现时绑定到调用方的值，之后必须一致；
/// 所有返回路径在调用方的同一点结束，区域内定义的值不在区域外使用，区域内的块只从区域内进入。
/// 证明成立时这段区域换成一次调用（标为内联，执行对照按被调方法的 IL 执行）；仍未覆盖的不可访问访问记为洞。
/// </summary>
internal sealed partial class TemplateRecovery
{
    /// <summary>路径上的读取：Read 是归一后的位置，Epoch 是此前经过的调用数（调用可能改写任意位置）。</summary>
    private sealed record Observed(ManagedValue Read, int Epoch) : ManagedValue(Read.Type, Read.Width);
    /// <summary>区域内第 Index 次调用的结果。</summary>
    private sealed record Returned(int Index, TypeRef Type, int Width) : ManagedValue(Type, Width);

    /// <summary>证明项的子项：带代数的读取继续遍历，调用结果是原子；其余沿用托管值结构。</summary>
    private static ManagedValue MapTerm(ManagedValue value, Func<ManagedValue, ManagedValue> map) => value switch
    {
        Observed observed => observed with { Read = map(observed.Read) },
        Returned => value,
        _ => ManagedValues.Map(value, map),
    };

    private sealed class Walker
    {
        public required IReadOnlyDictionary<ulong, ManagedBlock> Blocks { get; init; }
        public required bool Caller { get; init; }
        public ulong Block { get; set; }
        public int Index { get; set; }
        public Dictionary<Variable, ManagedValue> Env { get; init; } = [];
        public List<(ManagedValue Location, ManagedValue Value)> Stores { get; init; } = [];
        public HashSet<ulong> Visited { get; init; } = [];
        public int Epoch { get; set; }
        public int Calls { get; set; }
        public List<(ManagedValue Condition, bool Value)> Assumptions { get; init; } = [];
        /// <summary>这条路径上已经解引用过的项：它们非空，再次访问不会抛出。</summary>
        public HashSet<ManagedValue> Dereferenced { get; init; } = [];

        public ManagedStatement Current => Blocks[Block].Statements[Index];

        public Walker Clone() => new()
        {
            Blocks = Blocks, Caller = Caller, Block = Block, Index = Index, Env = new(Env), Stores = [.. Stores], Visited = [.. Visited], Epoch = Epoch, Calls = Calls, Assumptions = [.. Assumptions], Dereferenced = [.. Dereferenced],
        };
    }

    /// <summary>模板的一条路径在调用方的终点：出口位置、出口边上的复制、此时的环境与模板的返回值。</summary>
    private sealed record InlineEnd((ulong Block, int Index) Exit, IReadOnlyList<(LocalValue Target, ManagedValue Value)> Copies,
        IReadOnlyDictionary<Variable, ManagedValue> Env, ManagedValue? Result, bool Returns = false, int Epoch = 0)
    {
        /// <summary>这条路径结束时的写入与事实。</summary>
        public Walker? State { get; init; }
    }

    /// <summary>一次证明的结果：调用方区域的覆盖、各路径的终点，结论中的出口、出口复制与承接返回值的局部。</summary>
    private sealed class InlineMatch
    {
        public List<InlineEnd> Ends { get; } = [];
        /// <summary>证明不成立时第一处失败的说明。</summary>
        public string? Failure { get; set; }
        public bool Fail(string reason)
        {
            Failure ??= reason;
            return false;
        }
        public LocalValue? Result { get; set; }
        public required Dictionary<int, ManagedValue> Binding { get; init; }
        /// <summary>模板所属类型的实参：模板中的方法引用可能保留共享代码的开放形式，比较前代入。</summary>
        public required IReadOnlyList<TypeRef> TypeArguments { get; init; }
        public HashSet<(ulong Block, int Index)> Covered { get; } = [];
        /// <summary>区域内可能抛出的语句所在的块：只有它们受异常区域约束。</summary>
        public HashSet<ulong> Raising { get; } = [];
        /// <summary>调用方的显式判空：被判空的项与模板此刻解引用过的项。</summary>
        public List<(ManagedValue Actual, ManagedValue[] Dereferenced)> NullChecks { get; } = [];
        /// <summary>区域的第一个效果之前发生的读取。</summary>
        public HashSet<ManagedValue> EarlyReads { get; } = [];
        /// <summary>夹在模板写入之间的调用方写入，以及它之前已比对过的调用与检查数。</summary>
        public List<(ulong Block, int Index, int Effects)> Interleaved { get; } = [];
        /// <summary>区域内已比对的调用与检查：夹在其间的写入不能越过它们。</summary>
        public int Effects { get; set; }
        public (ulong Block, int Index)? Exit { get; set; }
        /// <summary>调用方区域的起点。</summary>
        public (ulong Block, int Index) Start { get; init; }
        public IReadOnlyList<(LocalValue Target, ManagedValue Value)>? ExitCopies { get; set; }
        public Dictionary<Variable, ManagedValue> Defined { get; } = [];
        public Dictionary<Variable, LocalValue> Locals { get; } = [];
        /// <summary>区域内异常边 φ 的赋值：与模板无关，换成调用时提到调用之前。</summary>
        public List<ManagedAssignment> Arrivals { get; } = [];
        public ManagedBranch? Continuation { get; set; }
        public bool Returns { get; set; }
        public List<(ManagedValue Value, LocalValue Local)> Inputs { get; } = [];
    }

    /// <summary>每个待证访问（按原生地址）第一次尝试的失败原因，写入洞的说明。</summary>
    private readonly Dictionary<ulong, string> inlineFailures = [];

    private ManagedValue? hollow;
    private ManagedValue Hollow => hollow ??= new ConstantValue(0, types.Boolean, 0);

    /// <summary>对方法体反复寻找可证明的内联区域，直到没有新的证明；之后把仍未覆盖的不可访问访问与未证明的构造换成洞。</summary>
    private ManagedBody InlineInverse(ManagedBody body)
    {
        body = ResolveAccessors(body);
        body = InlineConstructions(body);
        // 一轮里失败过的语句不再重试；有证明成立时再来一轮，方法体变了可能使它成立。
        var failed = new HashSet<ManagedStatement>(ReferenceEqualityComparer.Instance);
        var progressed = false;
        while (true)
        {
            var pending = Pending(body).ToArray();
            var statements = body.Blocks.ToDictionary(b => b.Address, b => b.Statements);
            var candidates = pending.Where(p => !failed.Contains(statements[p.Block][p.Index])).Take(1).ToArray();
            if (candidates is not [var candidate])
            {
                if (!progressed) break;
                progressed = false;
                failed.Clear();
                continue;
            }
            var next = TryInline(body, candidate);
            if (next is not null) next = DeadPendingReads(next);
            // 每次证明必须减少待证访问，终止条件不依赖方法中内联调用的数量。
            if (next is null || Pending(next).Count() >= pending.Length)
            {
                failed.Add(statements[candidate.Block][candidate.Index]);
                continue;
            }
            body = next;
            progressed = true;
        }
        body = DeadPendingReads(body);
        // 未证明的访问：值与写入目标都换成洞。
        ManagedValue Seal(ManagedValue value)
        {
            if (PendingOf(value) is { } pending)
            {
                var reason = $"{pending.Reason}，也不在可证明的内联方法体中";
                if (inlineFailures.TryGetValue(pending.Address, out var failure)) reason += $"；内联证明：{failure}";
                holes.Add(new RecoveryHole(pending.Address, reason));
                return new HoleValue(reason, value.Type, value.Width);
            }
            return ManagedValues.Map(value, Seal);
        }
        return SealConstructions(ManagedValues.Map(body, Seal));
    }

    private IReadOnlyDictionary<Variable, PendingConstruction> pendingConstructions = new Dictionary<Variable, PendingConstruction>();
    private readonly Dictionary<Variable, string> constructionFailures = [];

    /// <summary>
    /// 构造函数的内联，以构造函数自身的恢复体为模板，与调用方区域同步执行证明：
    /// 新对象上的基类构造调用起的区域等于分配类型某个构造函数的执行时，写成对它的 newobj（透明）；
    /// 本类构造中缺少直接基类初始化时，与直接基类构造函数吻合的区域写成 base(...) 调用。
    /// </summary>
    private ManagedBody InlineConstructions(ManagedBody body)
    {
        body = InlineBaseConstructor(body);
        foreach (var (variable, pending) in pendingConstructions)
        {
            var failures = new List<string>();
            foreach (var definition in pending.Allocated.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
            {
                var method = new MethodRef(definition, pending.Allocated.Arguments, []);
                if (summaries(method) is not { Body: { } template }) { failures.Add(definition.Address == 0 ? "构造函数没有原生代码" : "构造函数自身未能恢复"); continue; }
                if (template.Regions.Count > 0 || !Acyclic(template)) { failures.Add("构造函数体含异常区域或环"); continue; }
                if (PendingCall(body, variable, pending) is not var (block, index, _)) break;
                var blocks = body.Blocks.ToDictionary(b => b.Address);
                string? nearest = null;
                var constructed = false;
                for (var start = 0; start <= index; start++)
                {
                    var match = Match(body, blocks, block, start, template, pending.Allocated.Arguments, out var failure);
                    if (match is not null && match.Covered.Contains((block, index))
                        && PlanReplacement(body, blocks, block, start, method, match, out failure) is { } replaced)
                    {
                        body = Constructed(replaced.Apply(body), variable, method);
                        failures.Clear();
                        constructed = true;
                        break;
                    }
                    nearest = failure;
                }
                if (constructed) break;
                failures.Add($"{definition.Name}({definition.Parameters.Count})：{nearest}");
            }
            if (failures.Count > 0 || PendingCall(body, variable, pending) is not null)
                constructionFailures[variable] = failures.Count == 0 ? "没有构造函数" : string.Join("；", failures.Distinct().Take(3));
        }
        return body;
    }

    /// <summary>等待证明的基类构造调用的位置与接收者。</summary>
    private static (ulong Block, int Index, LocalValue Receiver)? PendingCall(ManagedBody body, Variable variable, PendingConstruction pending)
    {
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is ManagedCall { Inlined: false, Invocation: { Receiver: LocalValue local } invocation }
                    && local.Variable.Equals(variable) && invocation.Method.Equals(pending.Base))
                    return (block.Address, i, local);
        return null;
    }

    /// <summary>证明成立的构造：对新对象调用分配类型构造函数的内联调用写成 newobj。</summary>
    private static ManagedBody Constructed(ManagedBody body, Variable variable, MethodRef constructor) => body with
    {
        Blocks = body.Blocks.Select(b => b with
        {
            Statements = b.Statements.Select(s => s is ManagedCall { Inlined: true, Invocation: { Receiver: LocalValue local } invocation } call
                && local.Variable.Equals(variable) && invocation.Method.Equals(constructor)
                ? new ManagedAssignment(call.Address, local, new NewObjectValue(constructor, invocation.Arguments) { Transparent = true })
                : s).ToArray(),
        }).ToArray(),
    };

    /// <summary>未证明的构造：基类构造调用和接收者使用保留缺口。</summary>
    private ManagedBody SealConstructions(ManagedBody body)
    {
        foreach (var (variable, pending) in pendingConstructions)
        {
            if (PendingCall(body, variable, pending) is not var (block, index, _)) continue;
            var reason = $"构造 {pending.Allocated} 的构造函数被内联为 {pending.Base}：{constructionFailures.GetValueOrDefault(variable) ?? "没有构造函数"}";
            holes.Add(new RecoveryHole(pending.Address, reason));
            body = body with
            {
                Blocks = body.Blocks.Select(b => b.Address != block ? b : b with
                {
                    Statements = b.Statements.Select((s, i) => i != index ? s
                        : new ManagedHole(pending.Address, $"构造 {pending.Allocated} 的构造函数被内联", false)).ToArray(),
                }).ToArray(),
            };
            ManagedValue Uninitialized(ManagedValue value) => value is LocalValue local && local.Variable == variable
                ? new HoleValue(reason, local.Type, local.Width) : ManagedValues.Map(value, Uninitialized);
            body = ManagedValues.Map(body, Uninitialized);
        }
        return body;
    }

    /// <summary>本类构造中被内联的直接基类构造，仍以基类原生方法体逐条证明，再恢复初始化调用。</summary>
    private ManagedBody InlineBaseConstructor(ManagedBody body)
    {
        if (body.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            || body.Method.DeclaringType is not DefinitionRef owner
            || owner.Definition.BaseType?.Substitute(owner.Arguments, []) is not DefinitionRef parent) return body;
        if (body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Invocation is
            { Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 } }
            && (c.Invocation.Method.DeclaringType.Equals(parent) || c.Invocation.Method.DeclaringType.Equals(owner)))) return body;
        foreach (var definition in parent.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
        {
            var method = new MethodRef(definition, parent.Arguments, []);
            if (summaries(method) is not { Body: { } template } || template.Regions.Count > 0 || !Acyclic(template)) continue;
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            foreach (var block in body.Blocks)
                for (var start = 0; start < block.Statements.Count; start++)
                {
                    if (block.Statements[start] is not (ManagedStore or ManagedCall or ManagedAssignment)) continue;
                    var match = Match(body, blocks, block.Address, start, template, parent.Arguments, out _);
                    if (match is not null && PlanReplacement(body, blocks, block.Address, start, method, match, out _) is { } replaced)
                        return replaced.Apply(body);
                }
        }
        return body;
    }

    private static PendingAccess? PendingOf(ManagedValue value) => value switch
    {
        FieldValue field => field.Pending,
        StaticFieldValue field => field.Pending,
        _ => null,
    };

    /// <summary>方法体中待证的不可访问访问：所在块、语句位置与访问本身（实例或静态字段）。</summary>
    private static IEnumerable<(ulong Block, int Index, ManagedValue Access)> Pending(ManagedBody body)
    {
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                foreach (var value in ManagedValues.Of(block.Statements[i]).Concat(ManagedValues.CopiedValues(block.Statements[i])).SelectMany(ManagedValues.Walk))
                    if (PendingOf(value) is not null) yield return (block.Address, i, value);
    }

    private ManagedBody? TryInline(ManagedBody body, (ulong Block, int Index, ManagedValue Access) anchor)
    {
        var (field, receiver) = anchor.Access switch
        {
            FieldValue access => (access.Field, access.Receiver.Type),
            StaticFieldValue access => (access.Field, (TypeRef?)null),
            _ => throw new InvalidOperationException(anchor.Access.ToString()),
        };
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var statements = blocks[anchor.Block].Statements;
        // 模板可能先调用其他方法再访问字段；同块的前导效果也须纳入逐项证明。
        var earliest = 0;
        // 字段可先读入局部，再跨过无关写入使用；保留原读取，只在已保存值可用的位置尝试替换。
        var latest = anchor.Index;
        if (statements[anchor.Index] is ManagedAssignment)
            while (latest + 1 < statements.Count && statements[latest] is ManagedAssignment or ManagedStore) latest++;
        var starts = Enumerable.Range(earliest, latest - earliest + 1).Select(i => (Block: anchor.Block, Index: i)).ToList();
        // 前导效果可能位于唯一前驱中，中间的空跳转不构成内联区域的边界。
        var visited = new HashSet<ulong> { anchor.Block };
        var current = anchor.Block;
        while (visited.Count < 16)
        {
            if (Predecessors(blocks, current) is not [var predecessor] || !visited.Add(predecessor.Address)) break;
            current = predecessor.Address;
            if (predecessor.Statements.All(s => s is ManagedJump { Edge.Copies.Count: 0 })) continue;
            starts.AddRange(Enumerable.Range(0, predecessor.Statements.Count).Select(i => (current, i)));
            break;
        }
        var failures = new List<(string Reason, int Progress)>();
        foreach (var (method, template) in InlineCandidates(field, receiver))
        {
            if (fields.CallFailure(method, receiver, receiver is null ? field.DeclaringType : null) is { } illegal) { failures.Add((illegal, -1)); continue; }
            // 失败原因取比对走得最远的起点：其他起点通常只是和这次访问无关。
            var (nearest, progress) = ((string?)null, -1);
            foreach (var (block, start) in starts)
            {
                var match = Match(body, blocks, block, start, template, method.TypeArguments, out var failure);
                if (match is not null && PlanReplacement(body, blocks, block, start, method, match, out failure) is { } replaced)
                    return replaced.Apply(body);
                if (lastProgress > progress) (nearest, progress) = (failure, lastProgress);
            }
            failures.Add(($"{method.Method.Owner.Name}.{method.Method.Name}：{nearest}", progress));
        }
        // 方法体随证明变化，留下最后一次尝试的原因。
        inlineFailures[PendingOf(anchor.Access)!.Address] = failures.Count == 0 ? "没有可作模板的方法"
            : string.Join("；", failures.OrderByDescending(f => f.Progress).Take(3).Select(f => f.Reason));
        return null;
    }

    private readonly Dictionary<(FieldRef, TypeRef?), IReadOnlyList<(MethodRef, ManagedBody)>> inlineCandidates = [];

    /// <summary>
    /// 多语句模板：共同候选（<see cref="InlineEvidence.Candidates"/>）中访问该字段、方法体无环且没有异常区域的非泛型方法。
    /// 次序是启发式：先试含写入的模板，再按方法体从小到大；任何证明成立的模板都与原生代码等价，次序只影响选中哪一个。
    /// </summary>
    private IReadOnlyList<(MethodRef Method, ManagedBody Body)> InlineCandidates(FieldRef field, TypeRef? receiver)
    {
        if (inlineCandidates.TryGetValue((field, receiver), out var known)) return known;
        inlineCandidates[(field, receiver)] = [];
        var found = new List<(MethodRef, ManagedBody)>();
        foreach (var method in fields.Candidates(field, receiver).Where(m => m.MethodArguments.Count == 0))
        {
            if (summaries(method) is not { Body: { } template } || template.Regions.Count > 0 || !Acyclic(template)) continue;
            var touches = template.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                .Any(v => FieldAccessor.FieldOf(v) is { } f && f.Field == field.Field);
            if (touches) found.Add((method, template));
        }
        IReadOnlyList<(MethodRef, ManagedBody)> sorted = found
            .OrderByDescending(f => f.Item2.Blocks.SelectMany(b => b.Statements).Any(s => s is ManagedStore))
            .ThenBy(f => f.Item2.Blocks.Sum(b => b.Statements.Count)).ToArray();
        return inlineCandidates[(field, receiver)] = sorted;
    }

    private static bool Acyclic(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var state = new Dictionary<ulong, int>();
        bool Visit(ulong address)
        {
            if (!blocks.TryGetValue(address, out var block)) return true;
            if (state.TryGetValue(address, out var s)) return s == 2;
            state[address] = 1;
            foreach (var edge in block.Statements.SelectMany(ManagedValues.Edges))
                if (!Visit(edge.Target)) return false;
            state[address] = 2;
            return true;
        }
        return Visit(body.Blocks[0].Address);
    }

    private readonly System.Runtime.CompilerServices.ConditionalWeakTable<IReadOnlyDictionary<ulong, ManagedBlock>, Dictionary<ulong, ManagedBlock[]>> predecessors = new();

    /// <summary>调用方块的前驱（重复的边算多个）；方法体大时比对会反复查询。</summary>
    private ManagedBlock[] Predecessors(IReadOnlyDictionary<ulong, ManagedBlock> blocks, ulong address) =>
        predecessors.GetValue(blocks, map => map.Values.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => e.Target).Distinct().Select(t => (t, b)))
            .GroupBy(p => p.t).ToDictionary(g => g.Key, g => g.Select(p => p.b).ToArray())).GetValueOrDefault(address) ?? [];

    /// <summary>最近一次比对覆盖的调用方语句数，用来挑选最接近成立的失败原因。</summary>
    private int lastProgress;

    /// <summary>以模板为准同步执行两边，返回调用方区域的覆盖与出口；不成立时为 null。</summary>
    private InlineMatch? Match(ManagedBody body, IReadOnlyDictionary<ulong, ManagedBlock> callerBlocks, ulong block, int start, ManagedBody template, IReadOnlyList<TypeRef> arguments, out string failure)
    {
        failure = "接收者不能表示";
        var caller = new Walker { Blocks = callerBlocks, Caller = true, Block = block, Index = start };
        SeedPath(caller);
        caller.Visited.Add(block);
        // 模板的 this 在比对中绑定：可能是字段所在的对象，也可能是包含它的值（如嵌套类型的结构体）。
        var match = new InlineMatch { Binding = [], TypeArguments = arguments, Start = (block, start) };
        var entryLocals = callerBlocks.Values.SelectMany(b => b.Statements)
            .SelectMany(s => (s is ManagedAssignment assignment ? new[] { assignment.Target } : []).Concat(ManagedValues.Edges(s).SelectMany(e => e.Copies.Select(c => c.Target))))
            .DistinctBy(l => l.Variable).ToDictionary(l => l.Variable);
        foreach (var (variable, value) in caller.Env)
            if (entryLocals.TryGetValue(variable, out var local)) match.Inputs.Add((value, local));
        var callee = new Walker { Blocks = template.Blocks.ToDictionary(b => b.Address), Caller = false, Block = template.Blocks[0].Address, Index = 0 };
        var matched = Explore(callee, caller, match, 0) && ConcludeExit(match, template.Method, body, callerBlocks);
        if (matched && match.NullChecks.Any(c => !c.Dereferenced.Any(d => SameTerm(Bind(d, match.Binding), c.Actual))))
        {
            matched = false;
            match.Fail("调用方的判空对应不到模板的解引用");
        }
        lastProgress = match.Covered.Count;
        if (matched) return match;
        failure = match.Failure ?? "比对失败";
        return null;
    }

    /// <summary>区域内定义的局部（取赋值目标的类型）。</summary>
    private static LocalValue? LocalOf(InlineMatch match, Variable variable) => match.Locals.GetValueOrDefault(variable);

    private bool Explore(Walker callee, Walker caller, InlineMatch match, int depth)
    {
        if (depth > 32) return false;
        for (var steps = 0; steps < 256; steps++)
        {
            if (!Advance(callee, null)) return match.Fail("模板的值不能表示");
            if (callee.Current is ManagedReturn returned)
            {
                ManagedValue? value = null;
                if (returned.Value is { } v && (value = Term(callee, v)) is null) return match.Fail("模板的返回值不能表示");
                return Finish(caller, match, value);
            }
            if (callee.Current is ManagedBranch specialized && Term(callee, specialized.Condition) is { } test
                && KnownCondition(test, caller, match.Binding) is { } selected)
            {
                if (!Follow(callee, selected ? specialized.Taken : specialized.Fallthrough)) return false;
                continue;
            }
            if (callee.Current is ManagedCheck check && Term(callee, check.Condition) is { } checkedValue
                && KnownCondition(checkedValue, caller, match.Binding) == false) { callee.Index++; continue; }
            if (!Advance(caller, match)) return match.Fail($"调用方 0x{caller.Block:x} 的值不能表示或路径成环");
            var (m, c) = (callee.Current, caller.Current);
            if (m is ManagedCall { Invocation.Method.Method.Name: ".ctor" } constructor)
                m = constructor with { Invocation = ConstructorOrigin(constructor.Invocation) };
            if (c is ManagedCall { Invocation.Method.Method.Name: ".ctor" } actual)
                c = actual with { Invocation = ConstructorOrigin(actual.Invocation) };
            // 调用方的显式判空对应模板里随后的隐式解引用：两者抛出同样的异常，中间没有别的效果。
            if (c is ManagedCheck nullCheck && m is not ManagedCheck && AbsorbedNullCheck(nullCheck, callee, caller, match))
            {
                Cover(caller, match);
                caller.Index++;
                steps--;
                continue;
            }
            if (c is not ManagedStore) Cover(caller, match);
            switch (m, c)
            {
                case (ManagedStore, ManagedStore):
                    if (!MatchStores(callee, caller, match)) return false;
                    continue;
                case (ManagedCall mc, ManagedCall cc) when Instantiated(mc.Invocation.Method, match.TypeArguments).Equals(cc.Invocation.Method)
                    && mc.Invocation.Arguments.Count == cc.Invocation.Arguments.Count:
                    {
                        if ((mc.Invocation.Receiver is null) != (cc.Invocation.Receiver is null)) return false;
                        var pairs = (mc.Invocation.Receiver is { } mr ? [(mr, cc.Invocation.Receiver!)] : Array.Empty<(ManagedValue, ManagedValue)>())
                            .Concat(mc.Invocation.Arguments.Zip(cc.Invocation.Arguments));
                        foreach (var (a, b) in pairs)
                        {
                            if (Term(callee, a) is not { } ta || Term(caller, b) is not { } tb || !Same(ta, tb, caller, match.Binding)) return match.Fail($"调用 {cc.Invocation.Method.Method.Name} 的实参不同（0x{cc.Address:x}）");
                            NoteEarlyReads(tb, caller, match);
                        }
                        var index = callee.Calls++;
                        caller.Calls++;
                        match.Effects++;
                        if ((cc.Result ?? mc.Result) is { } kept)
                        {
                            var shared = new Returned(index, kept.Type, kept.Width);
                            if (mc.Result is { } mres) callee.Env[mres.Variable] = shared;
                            if (cc.Result is { } cres)
                            {
                                caller.Env[cres.Variable] = shared;
                                match.Defined[cres.Variable] = shared;
                                match.Locals[cres.Variable] = cres;
                            }
                        }
                        if (ManagedEffects.Invocation(cc.Invocation).InvalidatesMemory)
                        {
                            callee.Epoch++; caller.Epoch++;
                            callee.Stores.Clear(); caller.Stores.Clear();
                        }
                        break;
                    }
                case (ManagedCheck mk, ManagedCheck ck) when mk.Exception.Equals(ck.Exception):
                    if (Term(callee, mk.Condition) is not { } mtest || Term(caller, ck.Condition) is not { } ctest || !Same(mtest, ctest, caller, match.Binding)) return match.Fail($"检查条件不同（0x{ck.Address:x}）");
                    match.Effects++;
                    break;
                case (ManagedThrow mt, ManagedThrow ct):
                    return Term(callee, mt.Exception) is { } me && Term(caller, ct.Exception) is { } ce && Same(me, ce, caller, match.Binding);
                case (ManagedBranch mb, ManagedBranch cb):
                    {
                        if (Term(callee, mb.Condition) is not { } mcond || Term(caller, cb.Condition) is not { } ccond) return false;
                        bool crossed;
                        var trial = new Dictionary<int, ManagedValue>(match.Binding);
                        if (Same(mcond, ccond, caller, trial)) crossed = false;
                        else if (Same(mcond, Negate(ccond), caller, trial = new(match.Binding))) crossed = true;
                        else return match.Fail($"分支条件不同（0x{cb.Address:x}）");
                        foreach (var (key, value) in trial) match.Binding[key] = value;
                        var (mTaken, mFall) = (callee.Clone(), callee);
                        var (cTaken, cFall) = (caller.Clone(), caller);
                        cTaken.Assumptions.Add((ccond, !crossed));
                        cFall.Assumptions.Add((ccond, crossed));
                        if (!Follow(mTaken, mb.Taken) || !Follow(mFall, mb.Fallthrough)) return false;
                        if (!Follow(cTaken, crossed ? cb.Fallthrough : cb.Taken) || !Follow(cFall, crossed ? cb.Taken : cb.Fallthrough)) return false;
                        return Explore(mTaken, cTaken, match, depth + 1) && Explore(mFall, cFall, match, depth + 1);
                    }
                default:
                    return match.Fail($"模板的 {m.GetType().Name[7..]} 对应调用方的 {c.GetType().Name[7..]}（0x{c.Address:x}）");
            }
            callee.Index++;
            caller.Index++;
        }
        return false;
    }

    /// <summary>
    /// 一段连续写入按偏序比对：模板的写入两两不别名时没有先后，调用方可按任意次序完成。夹在其间的调用方自身写入移出区域：
    /// 它之前没有调用或检查时提到区域之前，之后没有时留到区域之后，两者都不越过任何可观察的次序；否则证明不成立。
    /// </summary>
    private bool MatchStores(Walker callee, Walker caller, InlineMatch match)
    {
        var remaining = new List<(ManagedValue Location, ManagedValue Value)>();
        while (callee.Current is ManagedStore store)
        {
            if (Location(callee, store.Target) is not { } location || Term(callee, store.Value) is not { } value) return match.Fail("模板的写入不能表示");
            remaining.Add((location, value));
            callee.Stores.Add((location, value));
            callee.Index++;
            if (!Advance(callee, null)) return match.Fail("模板的值不能表示");
        }
        // 这批写入涉及的对象：读取它们不会比写入先抛出空引用，不构成次序。
        var receivers = remaining.Select(r => ReceiverOf(r.Location)).OfType<ManagedValue>().ToHashSet();
        while (remaining.Count > 0)
        {
            if (!Advance(caller, match)) return match.Fail($"调用方 0x{caller.Block:x} 的值不能表示或路径成环");
            if (caller.Current is not ManagedStore written) return match.Fail($"模板的写入对应调用方的 {caller.Current.GetType().Name[7..]}（0x{caller.Current.Address:x}）");
            if (Location(caller, written.Target) is not { } target || Term(caller, written.Value) is not { } stored) return match.Fail("调用方的写入不能表示");
            var found = -1;
            for (var i = 0; i < remaining.Count && found < 0; i++)
            {
                var trial = new Dictionary<int, ManagedValue>(match.Binding);
                if (!Same(remaining[i].Location, target, caller, trial) || !Same(remaining[i].Value, stored, caller, trial)) continue;
                foreach (var (key, value) in trial) match.Binding[key] = value;
                found = i;
            }
            Cover(caller, match);
            if (found >= 0)
            {
                // 先于它完成的模板写入都要能交换到它之后。
                if (found > 0 && (!Unordered(remaining[found].Value, receivers)
                    || remaining.Take(found).Any(r => MayAlias(r.Location, remaining[found].Location) || !Unordered(r.Value, receivers))))
                    return match.Fail($"写入次序不同（0x{written.Address:x}）");
                remaining.RemoveAt(found);
                caller.Stores.Add((target, stored));
            }
            else
            {
                if (!Independent(stored) || remaining.Any(r => MayAlias(r.Location, target) || !Unordered(r.Value, receivers))
                    || caller.Stores.Any(s => MayAlias(s.Location, target)))
                    return match.Fail($"写入不同（0x{written.Address:x}）");
                match.Interleaved.Add((caller.Block, caller.Index, match.Effects));
                // 后面的读取可能看到它，比对时仍按已写入处理。
                caller.Stores.Add((target, stored));
            }
            caller.Index++;
        }
        return true;
    }

    private static ManagedValue? ReceiverOf(ManagedValue location) => location switch
    {
        FieldValue field => field.Receiver,
        ArrayElementValue element => element.Array,
        _ => null,
    };

    /// <summary>
    /// 写入的值和其他写入没有次序：它的项在写入之前已经确定（读取已按路径上的写入归一），求值本身也看不出先后。
    /// 分配、调用或可能抛出其他异常的项不行；读取只接受这批写入涉及的对象，空引用在任何次序下都发生在第一次访问。
    /// </summary>
    private static bool Unordered(ManagedValue value, IReadOnlySet<ManagedValue> receivers) => value switch
    {
        ArgumentValue or ConstantValue or LocalValue or Returned => true,
        Observed { Read: FieldValue field } => receivers.Contains(field.Receiver) || field.Receiver is Observed && Unordered(field.Receiver, receivers),
        ComposedValue composed => composed.Leaves.All(l => Unordered(l.Value, receivers)),
        BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr } binary
            => Unordered(binary.Left, receivers) && Unordered(binary.Right, receivers),
        ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => Unordered(conversion.Operand, receivers),
        ComparisonValue comparison => Unordered(comparison.Left, receivers) && Unordered(comparison.Right, receivers),
        NegatedValue negated => Unordered(negated.Operand, receivers),
        _ => false,
    };

    /// <summary>移出区域的调用方写入，只有形参、区域外的局部和常量组成的值：放到区域前后值都不变。</summary>
    private static bool Independent(ManagedValue value) => value is ArgumentValue or ConstantValue or LocalValue
        || value is ComposedValue composed && composed.Leaves.All(l => Independent(l.Value));

    private static MethodRef Instantiated(MethodRef method, IReadOnlyList<TypeRef> arguments) => method with
    {
        TypeArguments = method.TypeArguments.Select(t => t.Substitute(arguments, [])).ToArray(),
        MethodArguments = method.MethodArguments.Select(t => t.Substitute(arguments, [])).ToArray(),
    };

    /// <summary>形参可能还没有绑定，这里只记下判空的项和模板此刻解引用过的项，比对结束后按最终绑定核对。</summary>
    private bool AbsorbedNullCheck(ManagedCheck check, Walker callee, Walker caller, InlineMatch match)
    {
        if (check.Exception.DeclaringType is not DefinitionRef { Definition.FullName: "System.NullReferenceException" }
            || check.Condition is not ComparisonValue { Condition: Cond.Eq, Right: ConstantValue { Bits: 0 }, Left: var tested }
            || Term(caller, tested) is not { } actual) return false;
        match.NullChecks.Add((actual, callee.Dereferenced.ToArray()));
        return true;
    }

    /// <summary>记下调用方在区域的第一个效果之前读取的项（判空不算效果：与读取抛出同样的异常）。</summary>
    private static void NoteEarlyReads(ManagedValue term, Walker caller, InlineMatch match)
    {
        if (match.Effects > 0 || caller.Stores.Count > 0) return;
        void Visit(ManagedValue value)
        {
            if (value is Observed) match.EarlyReads.Add(value);
            MapTerm(value, child => { Visit(child); return child; });
        }
        Visit(term);
    }

    private void Cover(Walker caller, InlineMatch match)
    {
        match.Covered.Add((caller.Block, caller.Index));
        if (Raises(caller, caller.Current)) match.Raising.Add(caller.Block);
        NoteAccesses(caller, caller.Current);
    }

    /// <summary>推进到下一个事件：赋值与跳转（含边上的并行复制）只改变环境。调用方的赋值记入覆盖与区域内定义。</summary>
    private bool Advance(Walker walker, InlineMatch? match)
    {
        for (var steps = 0; steps < 256; steps++)
        {
            if (walker.Index >= walker.Blocks[walker.Block].Statements.Count) return false;
            switch (walker.Current)
            {
                case ManagedAssignment { ExceptionArrival: true } arrival when match is not null:
                    Cover(walker, match);
                    match.Arrivals.Add(arrival);
                    walker.Index++;
                    continue;
                case ManagedAssignment assignment:
                    if (Term(walker, assignment.Value) is not { } value) return false;
                    if (match is not null) { Cover(walker, match); NoteEarlyReads(value, walker, match); }
                    else NoteAccesses(walker, assignment);
                    walker.Env[assignment.Target.Variable] = value;
                    if (match is not null)
                    {
                        match.Defined[assignment.Target.Variable] = value;
                        match.Locals[assignment.Target.Variable] = assignment.Target;
                    }
                    walker.Index++;
                    continue;
                case ManagedJump jump:
                    if (match is not null) Cover(walker, match);
                    if (!Follow(walker, jump.Edge)) return false;
                    continue;
                default:
                    return true;
            }
        }
        return false;
    }

    /// <summary>沿边进入后继：先求出全部复制的值再写入（并行复制）；同一路径不重复进入一个块。</summary>
    private bool Follow(Walker walker, ManagedEdge edge)
    {
        var values = new List<(Variable, ManagedValue)>();
        foreach (var copy in edge.Copies)
        {
            if (Term(walker, copy.Value) is not { } value) return false;
            values.Add((copy.Target.Variable, value));
        }
        foreach (var (variable, value) in values) walker.Env[variable] = value;
        if (!walker.Blocks.ContainsKey(edge.Target) || !walker.Visited.Add(edge.Target)) return false;
        walker.Block = edge.Target;
        walker.Index = 0;
        return true;
    }

    /// <summary>值在路径上的项：局部代入其定义（调用方区域外定义的局部保持原样）；读取按已知写入归一。</summary>
    private ManagedValue? Term(Walker walker, ManagedValue value)
    {
        switch (value)
        {
            case LocalValue local:
                return walker.Env.TryGetValue(local.Variable, out var bound) ? bound : walker.Caller ? local : null;
            case HoleValue:
                return null;
            case FieldValue field:
                return Term(walker, field.Receiver) is { } receiver ? Load(walker, new FieldValue(receiver, field.Field, field.Type, field.Width)) : null;
            case StaticFieldValue field:
                return Load(walker, new StaticFieldValue(field.Field, field.Type, field.Width));
            case ArrayElementValue element:
                return Term(walker, element.Array) is { } array && Term(walker, element.Index) is { } index ? Load(walker, element with { Array = array, Index = index }) : null;
        }
        var failed = false;
        var mapped = ManagedValues.Map(value, child =>
        {
            if (Term(walker, child) is { } term) return term;
            failed = true;
            return child;
        });
        return failed ? null : mapped;
    }

    /// <summary>写入目标的位置项。</summary>
    private ManagedValue? Location(Walker walker, ManagedValue target) => target switch
    {
        FieldValue field => Term(walker, field.Receiver) is { } receiver ? new FieldValue(receiver, field.Field, field.Type, field.Width) : null,
        StaticFieldValue field => new StaticFieldValue(field.Field, field.Type, field.Width),
        ArrayElementValue element => Term(walker, element.Array) is { } array && Term(walker, element.Index) is { } index ? element with { Array = array, Index = index } : null,
        IndirectValue indirect => Term(walker, indirect.Address) is { } pointer ? indirect with { Address = pointer } : null,
        _ => null,
    };

    /// <summary>读取：路径上最近一次写入同一位置的值；可能别名的写入使读取不可判定；否则为本代的初始读取。</summary>
    private static ManagedValue? Load(Walker walker, ManagedValue location)
    {
        for (var i = walker.Stores.Count - 1; i >= 0; i--)
        {
            var (stored, value) = walker.Stores[i];
            if (stored.Equals(location)) return value;
            if (MayAlias(stored, location)) return null;
        }
        return new Observed(location, walker.Epoch);
    }

    /// <summary>
    /// 区域外使用的项（接收者、实参、出口复制）写回托管值。初代读取（此前没有经过调用）写成调用之前的读取，字段须可访问；
    /// 读取的接收者只接受调用方的 this、被内联方法的接收者，或读取本身发生在区域的任何效果之前：
    /// 前者非空，后两者为空时两种写法都在任何效果之前抛出 NullReferenceException。
    /// 调用结果与经过调用之后的读取不能写回。
    /// </summary>
    private ManagedValue? Materialize(ManagedValue term, ManagedValue? self, ulong address, InlineMatch match)
    {
        switch (term)
        {
            // 区域结束之后的读取：写在调用之后，字段访问照常接受证明。
            case Observed { Epoch: AfterRegion, Read: FieldValue field }:
                {
                    if (Materialize(field.Receiver, self, address, match) is not { } receiver) return null;
                    var access = new FieldValue(receiver, field.Field, field.Type, field.Width);
                    if (fields.Accessible(field.Field, receiver.Type)) return access;
                    return Accessor(field.Field, field.Type, false, receiver.Type) is { } accessor ? access with { Accessor = accessor }
                        : access with { Pending = new(address, $"内存 字段 {field.Field} 对调用方不可访问", false) };
                }
            case Observed { Epoch: AfterRegion, Read: StaticFieldValue field }:
                {
                    var access = new StaticFieldValue(field.Field, field.Type, field.Width);
                    if (fields.Accessible(field.Field, null)) return access;
                    return Accessor(field.Field, field.Type, false, null) is { } accessor ? access with { Accessor = accessor }
                        : access with { Pending = new(address, $"内存 字段 {field.Field} 对调用方不可访问", false) };
                }
            case Returned or Observed { Epoch: > 0 }:
                return null;
            case Observed { Read: FieldValue field }:
                {
                    if (!(field.Receiver.Equals(self) || field.Receiver is ArgumentValue { Index: -1 } || field.Receiver is Observed
                        || types.Kind(field.Receiver.Type) == TypeKind.Struct || match.EarlyReads.Contains(term))) return null;
                    if (Materialize(field.Receiver, self, address, match) is not { } receiver) return null;
                    var access = new FieldValue(receiver, field.Field, field.Type, field.Width);
                    if (fields.Accessible(field.Field, receiver.Type)) return access;
                    return Accessor(field.Field, field.Type, false, receiver.Type) is { } accessor ? access with { Accessor = accessor } : null;
                }
            case Observed { Read: StaticFieldValue field }:
                {
                    var access = new StaticFieldValue(field.Field, field.Type, field.Width);
                    if (fields.Accessible(field.Field, null)) return access;
                    return Accessor(field.Field, field.Type, false, null) is { } accessor ? access with { Accessor = accessor } : null;
                }
            case Observed:
                return null;
        }
        var failed = false;
        var mapped = ManagedValues.Map(term, child =>
        {
            if (Materialize(child, self, address, match) is { } value) return value;
            failed = true;
            return child;
        });
        return failed ? null : mapped;
    }

    /// <summary>模板的项 m 与调用方的项 c 相同：形参绑定到调用方的项（首次出现时绑定，之后须一致），其余逐层同形。</summary>
    private bool SameTerm(ManagedValue left, ManagedValue right) => Unify(left, right, [], false);

    private bool Unify(ManagedValue m, ManagedValue c, Dictionary<int, ManagedValue> binding, bool bindArguments = true)
    {
        m = NormalizeBit(m);
        c = NormalizeBit(c);
        if (m is ArgumentValue argument)
        {
            if (!bindArguments) return m.Equals(c);
            // 值类型字段的读取与写入共享同一个位置；ref 形参统一绑定到该位置的地址。
            if (argument.Type is ByRefRef reference && c.Type.Equals(reference.Element)
                && c is Observed { Read: FieldValue or StaticFieldValue or ArrayElementValue } or LocalValue or ArgumentValue)
                c = new AddressValue(c);
            if (binding.TryGetValue(argument.Index, out var bound)) return SameTerm(bound, c);
            binding[argument.Index] = c;
            return true;
        }
        switch (m, c)
        {
            case (Observed a, Observed b): return a.Epoch == b.Epoch && Unify(a.Read, b.Read, binding, bindArguments);
            case (Returned a, Returned b): return a.Index == b.Index && a.Type.Equals(b.Type);
            case (Observed or Returned, _) or (_, Observed or Returned): return false;
        }
        var sameShape = (m, c) switch
        {
            (NewObjectValue a, NewObjectValue b) => a.Constructor.Equals(b.Constructor) && a.Transparent == b.Transparent && a.Arguments.Count == b.Arguments.Count,
            (ComposedValue a, ComposedValue b) => a.Type.Equals(b.Type) && a.Leaves.Count == b.Leaves.Count && a.Leaves.Zip(b.Leaves).All(p => p.First.Path.SequenceEqual(p.Second.Path)),
            _ => m.GetType() == c.GetType() && ManagedValues.Map(m, _ => Hollow).Equals(ManagedValues.Map(c, _ => Hollow)),
        };
        if (!sameShape) return false;
        var (left, right) = (ManagedValues.Children(m).ToArray(), ManagedValues.Children(c).ToArray());
        return left.Length == right.Length && left.Zip(right).All(p => Unify(p.First, p.Second, binding, bindArguments));
    }

    /// <summary>模板的项与调用方的项在调用方这条路径的事实下相同。</summary>
    private bool Same(ManagedValue template, ManagedValue actual, Walker caller, Dictionary<int, ManagedValue> binding) =>
        Unify(Canonical(Fold(Specialize(template, caller, binding))), Canonical(Fold(Specialize(actual, caller, NoBinding))), binding);

    private static readonly Dictionary<int, ManagedValue> NoBinding = [];

    /// <summary>比较的规范形：大于、大于等于交换操作数写成小于、小于等于。</summary>
    private static ManagedValue Canonical(ManagedValue condition) => condition switch
    {
        ComparisonValue { Condition: Cond.Sgt } c => c with { Condition = Cond.Slt, Left = c.Right, Right = c.Left },
        ComparisonValue { Condition: Cond.Sge } c => c with { Condition = Cond.Sle, Left = c.Right, Right = c.Left },
        ComparisonValue { Condition: Cond.Ugt } c => c with { Condition = Cond.Ult, Left = c.Right, Right = c.Left },
        ComparisonValue { Condition: Cond.Uge } c => c with { Condition = Cond.Ule, Left = c.Right, Right = c.Left },
        _ => condition,
    };

    private ManagedValue Negate(ManagedValue condition) => condition switch
    {
        ComparisonValue c when Negated(c.Condition) is { } negated => c with { Condition = negated },
        NegatedValue n => n.Operand,
        _ => new NegatedValue(condition, types.Boolean),
    };

    private static Cond? Negated(Cond condition) => condition switch
    {
        Cond.Eq => Cond.Ne, Cond.Ne => Cond.Eq,
        Cond.Slt => Cond.Sge, Cond.Sge => Cond.Slt, Cond.Sle => Cond.Sgt, Cond.Sgt => Cond.Sle,
        Cond.Ult => Cond.Uge, Cond.Uge => Cond.Ult, Cond.Ule => Cond.Ugt, Cond.Ugt => Cond.Ule,
        // 浮点比较的取反把 NaN 归到另一侧。
        Cond.FEq => Cond.FUne, Cond.FUne => Cond.FEq, Cond.FNe => Cond.FUeq, Cond.FUeq => Cond.FNe,
        Cond.FLt => Cond.FUge, Cond.FUge => Cond.FLt, Cond.FLe => Cond.FUgt, Cond.FUgt => Cond.FLe,
        Cond.FGt => Cond.FUle, Cond.FUle => Cond.FGt, Cond.FGe => Cond.FUlt, Cond.FUlt => Cond.FGe,
        Cond.FOrdered => Cond.FUnordered, Cond.FUnordered => Cond.FOrdered,
        _ => null,
    };

    /// <summary>
    /// 结果不再使用的待证字段读取（内联区域换成调用后，区域之前读入的值常只剩这一用途）：读取没有副作用，
    /// 引用接收者保留原位置的判空，值类型接收者保留其求值；不留下不可访问的死字段。
    /// </summary>
    private ManagedBody DeadPendingReads(ManagedBody body)
    {
        var used = body.Blocks.SelectMany(b => b.Statements)
            .SelectMany(s => (s is ManagedAssignment a ? [a.Value] : ManagedValues.Of(s)).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
            .OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
        var nullConstructor = new MethodRef(types.Corlib("System.NullReferenceException").Definition.Methods
            .Single(m => m.Name == ".ctor" && m.Parameters.Count == 0), [], []);
        ManagedStatement Rewrite(ManagedStatement statement)
        {
            if (statement is not ManagedAssignment { Target: var target, Value: FieldValue { Pending: not null } field }
                || used.Contains(target.Variable)) return statement;
            var receiver = field.Receiver;
            if (ManagedTypes.IsReferenceType(receiver.Type))
                return new ManagedCheck(statement.Address, new ComparisonValue(Cond.Eq, receiver,
                    new ConstantValue(0, receiver.Type, 64), types.Boolean), nullConstructor);
            if (receiver.Type is ByRefRef reference) receiver = new IndirectValue(receiver, reference.Element, Width(reference.Element));
            return new ManagedAssignment(statement.Address, NewLocal(receiver.Type), receiver);
        }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(Rewrite).ToArray() }).ToArray() };
    }
}
