using System.Reflection;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

/// <summary>新对象的基类构造已下降，分配类型的构造仍待模板证明。</summary>
internal sealed record PendingConstruction(ulong Address, DefinitionRef Allocated, MethodRef Base);

/// <summary>内联逆的结果；Rules 是按原生代码直接写出的访问（inline.unfolded）与成立的内联证明（inline.proof）。</summary>
internal sealed record TemplateResult(ManagedBody Body, IReadOnlyList<RecoveryHole> Holes, IReadOnlyList<Cpp2CS.Diagnostics.RuleTrace> Rules);

/// <summary>
/// 内联逆（模型见 docs 的内联证明理论）：调用方中一段代码与一次调用的行为等价时，把它换成这次调用。
/// 锚点是待证访问（对调用方不可访问的字段）与待证构造；候选模板来自 <see cref="InlineEvidence"/>；
/// 每个候选替换都经复核（原方法体与展开新调用后的方法体共同执行）才采用。访问器与值类型构造按模板的语义摘要判定。
/// 证明不成立的访问在收尾时按原生代码写出（同程序集）或记为洞。
/// </summary>
internal sealed class InlineProof
{
    internal const string UnfoldedRule = "inline.unfolded";
    internal const string ProofRule = "inline.proof";

    private readonly ManagedTypes types;
    private readonly MethodRef caller;
    private readonly Func<MethodRef, MethodRecoveryResult?> summaries;
    private readonly InlineEvidence evidence;
    private readonly TemplateSummaries semantic;
    private readonly Dictionary<MethodRef, Program?> programs = [];
    private readonly List<RecoveryHole> holes = [];
    private readonly List<Cpp2CS.Diagnostics.RuleTrace> rules = [];
    private readonly Dictionary<ulong, string> failures = [];
    private int nextLocal;

    public InlineProof(ManagedTypes types, MethodRef caller, Func<MethodRef, MethodRecoveryResult?> summaries, InlineEvidence evidence)
    {
        (this.types, this.caller, this.summaries, this.evidence) = (types, caller, summaries, evidence);
        semantic = new TemplateSummaries(types, evidence);
    }

    // ---- 模板 ----

    /// <summary>
    /// 方法的模板：它自身原生代码的恢复体。summaries 只给出与恢复上下文无关的结果（见 <see cref="MethodDecompiler.Template"/>），
    /// 这样的结果就是写出的方法体，模板的使用关系按完成次序无环。方法不以自身为模板；含异常区域或环的方法体不作模板。
    /// 发现、展开与复核都用这同一个模板。
    /// </summary>
    private Program? Template(MethodRef method)
    {
        if (programs.TryGetValue(method, out var known)) return known;
        programs[method] = null;
        if (method.Method == caller.Method || summaries(method) is not { Body: { } body } || body.Regions.Count > 0 || !Acyclic(body)) return null;
        return programs[method] = Program.Compile(body, types);
    }

    private static bool Acyclic(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var state = new Dictionary<ulong, int>();
        var stack = new Stack<(ulong Address, int Edge)>();
        stack.Push((body.Blocks[0].Address, 0));
        state[body.Blocks[0].Address] = 1;
        while (stack.TryPop(out var top))
        {
            var edges = blocks.TryGetValue(top.Address, out var block) ? block.Statements.SelectMany(ManagedValues.Edges).ToArray() : [];
            if (top.Edge >= edges.Length) { state[top.Address] = 2; continue; }
            stack.Push((top.Address, top.Edge + 1));
            var target = edges[top.Edge].Target;
            if (!state.TryGetValue(target, out var s)) { state[target] = 1; stack.Push((target, 0)); }
            else if (s == 1) return false;
        }
        return true;
    }

    private LocalValue NewLocal(TypeRef type) => new(new Variable(Storage.Temp(1000 + nextLocal++), 1), type, types.ValueWidth(type));

    private RegionProver Prover() => new(types, evidence, Template, NewLocal, Accessor);

    // ---- 预算 ----

    /// <summary>
    /// 一个方法的证明搜索总步数上限（各次尝试的步数之和）。尝试数是待证访问、候选、起点与重试轮数之积，单次尝试另有上限；
    /// 用尽后不再尝试，剩下的待证内容记为预算用尽。按步数而非时间计，结果可复现。
    /// </summary>
    private const long MethodSteps = 1_000_000;
    private const string Exhausted = "内联证明的步数预算用尽";
    private long spent;

    private bool Spent => spent >= MethodSteps;

    private RegionProver.Outcome Prove(RegionProver prover, Program program, EntryFacts facts, ulong block, int index, Candidate candidate, Func<TracePoint, bool> anchor,
        Func<ManagedBody, bool>? useful = null)
    {
        var outcome = prover.Prove(program, facts, block, index, candidate, anchor, useful);
        spent += outcome.Steps;
        return outcome;
    }

    // ---- 入口 ----

    public TemplateResult Run(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, int firstLocal)
    {
        holes.Clear();
        rules.Clear();
        failures.Clear();
        spent = 0;
        nextLocal = firstLocal;
        if (InlineTrace.For(caller.Method)) InlineTrace.Before?.Invoke(body);
        body = ResolveAccessors(body);
        body = BaseConstructor(body);
        var constructionFailures = new Dictionary<Variable, string>();
        body = Constructions(body, constructions, constructionFailures);
        body = Accesses(body);
        body = DeadPendingReads(OverlaidReads(body));
        body = Seal(body);
        body = SealConstructions(body, constructions, constructionFailures);
        return new(body, holes.ToArray(), rules.ToArray());
    }

    private ManagedBody Adopt(ManagedBody replaced, ulong at, string form, MethodRef method)
    {
        rules.Add(new Cpp2CS.Diagnostics.RuleTrace(ProofRule, at, Cpp2CS.Diagnostics.RewriteStatus.Applied, form,
            $"{method.Method.Owner.FullName}.{method.Method.Name}", null));
        return replaced;
    }

    // ---- 待证访问 ----

    private static PendingAccess? PendingOf(ManagedValue value) => value switch
    {
        FieldValue field => field.Pending,
        StaticFieldValue field => field.Pending,
        _ => null,
    };

    private static IEnumerable<(ulong Block, int Index, ManagedValue Access)> Pending(ManagedBody body)
    {
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                foreach (var value in ManagedValues.Of(block.Statements[i]).Concat(ManagedValues.CopiedValues(block.Statements[i])).SelectMany(ManagedValues.Walk))
                    if (PendingOf(value) is not null) yield return (block.Address, i, value);
    }

    /// <summary>证明的进展：待证访问数，其次是读入待证访问的局部的使用数（一次读取可能被多个内联共用）。</summary>
    private static (int Pending, int Uses) Progress(ManagedBody body)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var held = Holding(body);
        return (Pending(body).Count(), statements.SelectMany(Program.Uses).Count(held.Contains));
    }

    /// <summary>一次证成的替换。Primary：待证访问减少；否则只减少了读入待证访问的局部的使用。</summary>
    private sealed record Replacement(ManagedBody Body, (int, int, int) Key, string Form, MethodRef Method, ulong At, bool Primary);

    /// <summary>
    /// 对方法体反复寻找可证明的内联区域，直到一轮没有新的证明。待证访问从后往前处理：区域的入口知识来自它之前的原代码，
    /// 前面的区域先换成调用会变成屏障，丢掉后面区域依赖的已知内容；后面的区域换成调用后，它用到的值在前面区域的出口也不再活跃。
    /// 进展分两级：待证访问减少的替换立即采纳；只减少读入值的使用的替换，只在一轮都没有前者时采纳最优的一个。
    /// 只覆盖使用的区域可能是更大内联体的一部分，过早换成调用会把那个内联体切碎。
    /// </summary>
    private ManagedBody Accesses(ManagedBody body)
    {
        // 失败按（语句，访问）记：同一语句里的另一个待证访问可能有别的候选。
        var failed = new HashSet<(ManagedStatement, ManagedValue)>(Identity.Instance);
        var progressed = false;
        // 本轮方法体未变时得到的次级替换。
        Replacement? secondary = null;
        while (true)
        {
            var statements = body.Blocks.ToDictionary(b => b.Address, b => b.Statements);
            var next = Pending(body).Reverse().FirstOrDefault(p => !failed.Contains((statements[p.Block][p.Index], p.Access)));
            if (next.Access is null)
            {
                if (!progressed && secondary is { } chosen)
                {
                    body = Adopt(chosen);
                    progressed = true;
                }
                if (!progressed) break;
                progressed = false;
                failed.Clear();
                secondary = null;
                continue;
            }
            var found = Inline(body, next);
            if (found is { Primary: true })
            {
                body = Adopt(found);
                progressed = true;
                secondary = null;
                continue;
            }
            failed.Add((statements[next.Block][next.Index], next.Access));
            if (found is not null && (secondary is null || found.Key.CompareTo(secondary.Key) < 0)) secondary = found;
        }
        return body;
    }

    private ManagedBody Adopt(Replacement replacement) => Adopt(replacement.Body, replacement.At, replacement.Form, replacement.Method);

    private sealed class Identity : IEqualityComparer<(ManagedStatement, ManagedValue)>
    {
        public static readonly Identity Instance = new();
        public bool Equals((ManagedStatement, ManagedValue) x, (ManagedStatement, ManagedValue) y) =>
            ReferenceEquals(x.Item1, y.Item1) && ReferenceEquals(x.Item2, y.Item2);
        public int GetHashCode((ManagedStatement, ManagedValue) key) =>
            HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Item1), System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Item2));
    }

    /// <summary>
    /// 锚点的候选起点：锚点所在块中锚点及之前的语句（从后往前）、唯一前驱链上的块、读入待证访问的局部之后的使用点。
    /// Covered 是起点到锚点之间含待证访问或使用其读入值的语句数（使用点为 0）。起点只影响能否找到证明，不影响正确性。
    /// </summary>
    private static List<(ulong Block, int Index, int Covered)> Starts(Program program, ulong block, int index, int events)
    {
        // 区域里的调用方事件都要与模板的事件对应：往回跨过的事件多于模板可能的事件数时，更早的起点不可能成立。
        var starts = new List<(ulong, int, int)>();
        var seen = new HashSet<(ulong, int)>();
        var holding = Holding(program.Body);
        var covered = 0;
        var crossed = 0;
        var current = block;
        var visited = new HashSet<ulong> { block };
        for (var i = index; ; )
        {
            for (; i >= 0 && crossed <= events; i--)
            {
                var statement = program.Blocks[current].Statements[i];
                if (HasPending(statement) || Program.Uses(statement).Any(holding.Contains)) covered++;
                if (seen.Add((current, i))) starts.Add((current, i, covered));
                crossed += program.EventsAt(current, i);
            }
            if (crossed > events || starts.Count >= 40 || program.Predecessors(current) is not [var predecessor] || !visited.Add(predecessor)) break;
            current = predecessor;
            i = program.Blocks[current].Statements.Count - 1;
        }
        // 共用的读取：读入局部之后的使用点。
        if (program.Blocks[block].Statements[index] is ManagedAssignment { Value: var value, Target.Variable: var held } && PendingOf(value) is not null)
        {
            var statements = program.Blocks[block].Statements;
            for (var i = index + 1; i < statements.Count && starts.Count < 48; i++)
                if (Program.Uses(statements[i]).Contains(held) && seen.Add((block, i))) starts.Add((block, i, 0));
        }
        return starts.Take(48).ToList();
    }

    /// <summary>读入待证访问的局部：区域覆盖它的使用也是进展（读取随之成为死代码）。</summary>
    private static HashSet<Variable> Holding(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements).OfType<ManagedAssignment>()
        .Where(a => PendingOf(a.Value) is not null).Select(a => a.Target.Variable).ToHashSet();

    private static bool HasPending(ManagedStatement statement) =>
        ManagedValues.Of(statement).Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk).Any(v => PendingOf(v) is not null);

    private (ManagedBody Body, Program Program, EntryFacts Facts)? analysis;
    private readonly HashSet<(ManagedBody, ulong, int)> traced = [];

    /// <summary>方法体的程序与起点事实；方法体不变时复用。</summary>
    private (Program Program, EntryFacts Facts) Analysis(ManagedBody body)
    {
        if (analysis is { } known && ReferenceEquals(known.Body, body)) return (known.Program, known.Facts);
        var program = Program.Compile(body, types);
        var facts = new EntryFacts(program, call => Template(call.Invocation.Method) is { } template && semantic.IsReadOnly(template));
        analysis = (body, program, facts);
        return (program, facts);
    }

    /// <summary>锚点上覆盖最多的替换；没有待证访问减少的替换时记下失败原因（次级替换仍返回，由调用者决定是否采纳）。</summary>
    private Replacement? Inline(ManagedBody body, (ulong Block, int Index, ManagedValue Access) anchor)
    {
        var (field, receiver) = anchor.Access switch
        {
            FieldValue access => (access.Field, access.Receiver.Type),
            StaticFieldValue access => (access.Field, (TypeRef?)null),
            _ => throw new InvalidOperationException(anchor.Access.ToString()),
        };
        if (Spent)
        {
            failures.TryAdd(PendingOf(anchor.Access)!.Address, Exhausted);
            return null;
        }
        var (program, facts) = Analysis(body);
        var before = Progress(body);
        // 区域要覆盖的语句：待证访问，或使用读入它的局部的语句（与进展的度量一致）。
        var holding = Holding(body);
        bool Gains(ManagedBody replaced)
        {
            var after = Progress(DeadPendingReads(replaced));
            return after.Pending < before.Pending || after.Pending == before.Pending && after.Uses < before.Uses;
        }
        bool Covers(TracePoint point) => point.Pending || Program.Uses(program.Blocks[point.Block].Statements[point.Statement]).Any(holding.Contains);
        var prover = Prover();
        var reasons = new List<(string Reason, int Progress)>();
        (ManagedBody Body, (int, int, int) Key, string Form, MethodRef Method, ulong At)? best = null;
        foreach (var (method, template) in Candidates(field, receiver))
        {
            if (Spent) { reasons.Add((Exhausted, int.MaxValue)); break; }
            if (evidence.CallFailure(method, receiver, receiver is null ? field.DeclaringType : null) is { } illegal) { reasons.Add((illegal, -1)); continue; }
            var (nearest, distance) = ((string?)null, -1);
            var reached = -1;
            foreach (var (block, index, covered) in Starts(program, anchor.Block, anchor.Index, template.EventBound))
            {
                // 已有成立的区域时，更远的起点只有多含待证访问才可能更优。
                if (covered <= reached) continue;
                if (Spent) break;
                if (InlineTrace.For(caller.Method) && traced.Add((body, block, index)))
                {
                    var at = facts.At(block, index);
                    InlineTrace.Write($"  事实 0x{block:x}:{index}（迭代 {facts.Visits}/{program.Blocks.Count} 块） 局部 {string.Join("，", at.Vars.Select(v => $"{v.Key}={v.Value}"))} 存储 {string.Join("，", at.Known.Select(k => $"{k.Key}={k.Value}"))}");
                }
                var started = System.Diagnostics.Stopwatch.GetTimestamp();
                var outcome = Prove(prover, program, facts, block, index, new Candidate(method, template, ReplacementKind.Call), Covers, Gains);
                (ManagedBody Body, (int, int, int) Key)? gained = null;
                if (outcome.Body is { } replaced)
                {
                    var next = DeadPendingReads(replaced);
                    var after = Progress(next);
                    // 取覆盖最多的区域：剩下的待证访问最少，其次读入的使用最少，再次区域最长。较小的区域会把同一个调用切成片段。
                    if (after.Pending < before.Pending || after.Pending == before.Pending && after.Uses < before.Uses)
                        gained = (next, (after.Pending, after.Uses, -outcome.Progress));
                    else outcome = outcome with { Failure = $"证明成立但待证访问没有减少（{before.Pending}/{before.Uses} → {after.Pending}/{after.Uses}）" };
                }
                if (InlineTrace.For(caller.Method))
                    InlineTrace.Write($"  内联 {field.Field.Name}@0x{anchor.Block:x}:{anchor.Index} {method.Method.Owner.Name}.{method.Method.Name} 起点 0x{block:x}:{index} 进度 {outcome.Progress} 步 {outcome.Steps} {System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds:F0} ms（{outcome.Profile}）：{outcome.Failure ?? outcome.Form}");
                foreach (var note in InlineTrace.For(caller.Method) ? outcome.Plans : []) InlineTrace.Write($"    方案 {note}");
                if (gained is { } g)
                {
                    if (best is null || g.Key.CompareTo(best.Value.Key) < 0)
                        best = (g.Body, g.Key, outcome.Form, method, program.Blocks[block].Statements[index].Address);
                    reached = Math.Max(reached, covered);
                    continue;
                }
                if (outcome.Progress > distance) (nearest, distance) = (outcome.Failure, outcome.Progress);
            }
            reasons.Add(($"{method.Method.Owner.Name}.{method.Method.Name}：{nearest}", distance));
        }
        var result = best is { } chosen ? new Replacement(chosen.Body, chosen.Key, chosen.Form, chosen.Method, chosen.At, chosen.Key.Item1 < before.Pending) : null;
        if (result is not { Primary: true })
            failures.TryAdd(PendingOf(anchor.Access)!.Address, reasons.Count == 0 ? "没有可作模板的方法"
                : string.Join("；", reasons.OrderByDescending(r => r.Progress).Take(3).Select(r => r.Reason)));
        return result;
    }

    private readonly Dictionary<(FieldRef, TypeRef?), IReadOnlyList<(MethodRef, Program)>> candidates = [];

    /// <summary>
    /// 访问该字段的候选模板：共同候选（<see cref="InlineEvidence.Candidates"/>）中方法体提到该字段的非泛型方法；
    /// 值类型的字段另加该类型带参数的构造函数（x = new T(...) 是对 x 的实例调用）。先试含写入的、再按方法体从小到大。
    /// </summary>
    private IReadOnlyList<(MethodRef Method, Program Template)> Candidates(FieldRef field, TypeRef? receiver)
    {
        if (candidates.TryGetValue((field, receiver), out var known)) return known;
        var methods = evidence.Candidates(field, receiver).Where(m => m.MethodArguments.Count == 0);
        if (field.DeclaringType is DefinitionRef owner && types.Kind(owner) == TypeKind.Struct && !field.Field.IsStatic)
            methods = methods.Concat(owner.Definition.Methods.Where(m => m.Name == ".ctor" && m.GenericParameters.Count == 0 && m.Parameters.Count > 0)
                .Select(m => new MethodRef(m, owner.Arguments, [])));
        var found = new List<(MethodRef, Program)>();
        foreach (var method in methods)
        {
            if (Template(method) is not { } template) continue;
            var touches = template.Body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).Any(v => FieldAccessor.FieldOf(v) is { } f && f.Field == field.Field);
            if (touches) found.Add((method, template));
        }
        IReadOnlyList<(MethodRef, Program)> sorted = found
            .OrderByDescending(f => f.Item2.Body.Blocks.SelectMany(b => b.Statements).Any(s => s is ManagedStore))
            .ThenBy(f => f.Item2.Body.Blocks.Sum(b => b.Statements.Count)).ToArray();
        return candidates[(field, receiver)] = sorted;
    }

    // ---- 构造 ----

    private static (ulong Block, int Index)? PendingCall(ManagedBody body, Variable variable, PendingConstruction pending)
    {
        foreach (var block in body.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                if (block.Statements[i] is ManagedCall { Inlined: false, Invocation: { Receiver: LocalValue local } invocation }
                    && local.Variable.Equals(variable) && invocation.Method.Equals(pending.Base))
                    return (block.Address, i);
        return null;
    }

    /// <summary>
    /// 待证构造：分配与新对象上的基类构造调用起的区域，等于分配类型某个构造函数的 newobj 时，写成 newobj（透明）。
    /// 区域从分配处开始：新对象在第一次使用之前分配。
    /// </summary>
    private ManagedBody Constructions(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, Dictionary<Variable, string> failed)
    {
        foreach (var (variable, pending) in constructions)
        {
            if (PendingCall(body, variable, pending) is not var (block, index)) continue;
            var (program, facts) = Analysis(body);
            var statements = program.Blocks[block].Statements;
            var first = Enumerable.Range(0, index + 1).First(i => i == index || Program.Uses(statements[i]).Contains(variable));
            var local = program.LocalOf(variable)!;
            var prover = Prover();
            var reasons = new List<string>();
            var done = false;
            foreach (var definition in pending.Allocated.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
            {
                var method = new MethodRef(definition, pending.Allocated.Arguments, []);
                if (Template(method) is not { } template) { reasons.Add(definition.Address == 0 ? "构造函数没有原生代码" : "构造函数不能作模板"); continue; }
                string? nearest = null;
                for (var start = first; start >= 0 && !done; start--)
                {
                    if (Spent) { reasons.Add(Exhausted); break; }
                    var outcome = Prove(prover, program, facts, block, start, new Candidate(method, template, ReplacementKind.Construct, local),
                        point => point.Block == block && point.Statement == index);
                    if (InlineTrace.For(caller.Method))
                        InlineTrace.Write($"  构造 {pending.Allocated} {definition.Name}({definition.Parameters.Count}) 起点 0x{block:x}:{start} 进度 {outcome.Progress} 步 {outcome.Steps}：{outcome.Failure ?? outcome.Form}");
                    if (outcome.Body is { } replaced)
                    {
                        body = Adopt(replaced, statements[start].Address, $"construct+{outcome.Form}", method);
                        done = true;
                        break;
                    }
                    nearest ??= outcome.Failure;
                }
                if (done) break;
                reasons.Add($"{definition.Name}({definition.Parameters.Count})：{nearest}");
            }
            if (!done) failed[variable] = reasons.Count == 0 ? "没有构造函数" : string.Join("；", reasons.Distinct().Take(3));
        }
        return body;
    }

    /// <summary>未证明的构造：基类构造调用与新对象的使用保留缺口。</summary>
    private ManagedBody SealConstructions(ManagedBody body, IReadOnlyDictionary<Variable, PendingConstruction> constructions, Dictionary<Variable, string> failed)
    {
        foreach (var (variable, pending) in constructions)
        {
            if (PendingCall(body, variable, pending) is not var (block, index)) continue;
            var reason = $"构造 {pending.Allocated} 的构造函数被内联为 {pending.Base}：{failed.GetValueOrDefault(variable) ?? "没有构造函数"}";
            holes.Add(new RecoveryHole(pending.Address, reason));
            body = body with
            {
                Blocks = body.Blocks.Select(b => b.Address != block ? b : b with
                {
                    Statements = b.Statements.Select((s, i) => i != index ? s : new ManagedHole(pending.Address, $"构造 {pending.Allocated} 的构造函数被内联", false)).ToArray(),
                }).ToArray(),
            };
            ManagedValue Uninitialized(ManagedValue value) => value is LocalValue local && local.Variable == variable
                ? new HoleValue(reason, local.Type, local.Width) : ManagedValues.Map(value, Uninitialized);
            body = ManagedValues.Map(body, Uninitialized);
        }
        return body;
    }

    /// <summary>
    /// 构造函数中缺少直接基类（或本类）的构造调用：基类构造被内联了。与直接基类某个构造函数等价的区域写成 base(...)；
    /// 更远祖先的构造在比较中按模板展开。
    /// </summary>
    private ManagedBody BaseConstructor(ManagedBody body)
    {
        if (body.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            || body.Method.DeclaringType is not DefinitionRef owner
            || owner.Definition.BaseType?.Substitute(owner.Arguments, []) is not DefinitionRef parent
            || parent.Definition.FullName == "System.Object") return body;
        if (body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Invocation is { Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 } }
            && (c.Invocation.Method.DeclaringType.Equals(parent) || c.Invocation.Method.DeclaringType.Equals(owner)))) return body;
        var (program, facts) = Analysis(body);
        var prover = Prover();
        var starts = new List<(ulong, int)>();
        var current = program.Entry;
        var visited = new HashSet<ulong>();
        while (visited.Add(current) && starts.Count < 48)
        {
            starts.AddRange(Enumerable.Range(0, program.Blocks[current].Statements.Count).Select(i => (current, i)));
            if (program.Blocks[current].Statements[^1] is not ManagedJump { Edge.Target: var next }) break;
            current = next;
        }
        foreach (var definition in parent.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
        {
            var method = new MethodRef(definition, parent.Arguments, []);
            if (Template(method) is not { } template || evidence.CallFailure(method, new ArgumentValue(-1, owner, 64).Type, null) is not null) continue;
            foreach (var (block, index) in starts)
            {
                if (Spent) return body;
                var outcome = Prove(prover, program, facts, block, index, new Candidate(method, template, ReplacementKind.BaseConstructor), _ => true);
                if (InlineTrace.For(caller.Method))
                    InlineTrace.Write($"  基类构造 {parent} {definition.Parameters.Count} 起点 0x{block:x}:{index} 进度 {outcome.Progress} 步 {outcome.Steps}：{outcome.Failure ?? outcome.Form}");
                if (outcome.Body is { } replaced) return Adopt(replaced, program.Blocks[block].Statements[index].Address, $"base+{outcome.Form}", method);
            }
        }
        return body;
    }

    // ---- 访问器与值类型构造 ----

    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), FieldAccessor?> accessors = [];
    private readonly Dictionary<(FieldRef, TypeRef, bool, TypeRef?), string> accessorFailures = [];

    /// <summary>候选方法按语义摘要恰为该字段的读取（getter）或写入（setter），且调用合法。</summary>
    public FieldAccessor? Accessor(FieldRef field, TypeRef valueType, bool write, TypeRef? receiver)
    {
        var key = (field, valueType, write, receiver);
        if (accessors.TryGetValue(key, out var known)) return known;
        accessors[key] = null;
        var owner = (DefinitionRef)field.DeclaringType;
        var isStatic = field.Field.IsStatic;
        FieldAccessor? found = null;
        var reasons = new List<string>();
        foreach (var method in evidence.Candidates(field, receiver))
        {
            var definition = method.Method;
            var receiverParameter = definition.IsStatic && !isStatic;
            var shape = write
                ? definition.Parameters.Count == 1 && ManagedTypes.IsVoid(definition.ReturnType) && definition.IsStatic == isStatic
                : !ManagedTypes.IsVoid(definition.ReturnType) && (receiverParameter
                    ? ManagedTypes.IsReferenceType(owner) && definition.Parameters.Count == 1 && method.Concrete(definition.Parameters[0].Type).Equals(owner)
                    : definition.Parameters.Count == 0 && definition.IsStatic == isStatic);
            if (!shape) continue;
            var declared = method.Concrete(write ? definition.Parameters[0].Type : definition.ReturnType);
            if (!declared.Equals(valueType) && (write || !ManagedTypes.IsReferenceType(valueType)
                || !ManagedTypes.IsReferenceType(declared) || !types.IsAssignable(valueType, declared))) continue;
            if (evidence.CallFailure(method, receiver, isStatic ? field.DeclaringType : null) is { } illegal) { reasons.Add(illegal); continue; }
            if (Template(method) is not { } template)
            {
                // 总被内联的库访问器：方法体按库的源码给出；自动属性的访问器按编译器的生成方式给出。
                if (!receiverParameter && (LibraryAccessors.IsAutoProperty(definition, field.Field, write) || !write && LibraryAccessors.IsRead(definition, field.Field)))
                {
                    found = new FieldAccessor(method, field, valueType, types.ValueWidth(valueType), write);
                    break;
                }
                reasons.Add(method.Method == caller.Method ? $"{definition.Name} 是调用方自身"
                    : summaries(method) is null ? $"{definition.Name} 没有原生入口" : $"{definition.Name} 不能作模板");
                continue;
            }
            if (!semantic.IsAccessor(template, field, write, receiverParameter)) { reasons.Add($"{definition.Name} 不是单一字段访问"); continue; }
            found = new FieldAccessor(method, field, valueType, types.ValueWidth(valueType), write);
            break;
        }
        accessorFailures[key] = reasons.Count == 0 ? "没有签名匹配的方法" : string.Join("；", reasons.Distinct().Take(3));
        return accessors[key] = found;
    }

    /// <summary>待证访问中有访问器的换成对访问器的调用（表达式级替换）；其余保持待证，并记下访问器失败的原因。</summary>
    private ManagedBody ResolveAccessors(ManagedBody body)
    {
        ManagedValue Resolve(ManagedValue value, bool target)
        {
            value = ManagedValues.Map(value, child => Resolve(child, false));
            return value switch
            {
                FieldValue { Pending: { } pending } field when pending.Write == target =>
                    Accessor(field.Field, field.Type, pending.Write, field.Receiver.Type) is { } accessor ? field with { Accessor = accessor, Pending = null }
                        : field with { Pending = WithAccessorFailure(pending, field.Field, field.Type, field.Receiver.Type) },
                StaticFieldValue { Pending: { } pending } field when pending.Write == target =>
                    Accessor(field.Field, field.Type, pending.Write, null) is { } accessor ? field with { Accessor = accessor, Pending = null }
                        : field with { Pending = WithAccessorFailure(pending, field.Field, field.Type, null) },
                _ => value,
            };
        }
        return ManagedValues.Map(body, v => Resolve(v, false), t => Resolve(t, true));
    }

    private PendingAccess WithAccessorFailure(PendingAccess pending, FieldRef field, TypeRef type, TypeRef? receiver) =>
        pending with { Reason = $"{pending.Reason}，没有可证明的访问器（{accessorFailures.GetValueOrDefault((field, type, pending.Write, receiver))}）" };

    public bool CanConstructValue(DefinitionRef structure) => semantic.CanConstructValue(structure, Template);

    public ValueConstruction? ProveValueConstruction(DefinitionRef structure, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves) =>
        semantic.Prove(structure, leaves, Template);

    // ---- 收尾 ----

    /// <summary>结果不再使用的待证读取只剩接收者为空时的异常：写成原位置的判空（或保留接收者的求值）。</summary>
    private ManagedBody DeadPendingReads(ManagedBody body)
    {
        var used = body.Blocks.SelectMany(b => b.Statements).SelectMany(Program.Uses).ToHashSet();
        var nullConstructor = new MethodRef(types.Corlib("System.NullReferenceException").Definition.Methods
            .Single(m => m.Name == ".ctor" && m.Parameters.Count == 0), [], []);
        ManagedStatement Rewrite(ManagedStatement statement)
        {
            if (statement is not ManagedAssignment { Target: var target, Value: FieldValue { Pending: not null } field } || used.Contains(target.Variable)) return statement;
            var receiver = field.Receiver;
            if (ManagedTypes.IsReferenceType(receiver.Type))
                return new ManagedCheck(statement.Address, new ComparisonValue(Cond.Eq, receiver, new ConstantValue(0, receiver.Type, 64), types.Boolean), nullConstructor);
            if (receiver.Type is ByRefRef reference) receiver = new IndirectValue(receiver, reference.Element, types.ValueWidth(reference.Element));
            return new ManagedAssignment(statement.Address, NewLocal(receiver.Type), receiver);
        }
        return body with { Blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(Rewrite).ToArray() }).ToArray() };
    }

    /// <summary>显式布局中不可访问字段的一段位片恰是另一个可访问字段时，读的是同一块存储，写成那个字段。</summary>
    private ManagedBody OverlaidReads(ManagedBody body)
    {
        static (FieldValue Field, int Shift)? Slice(ManagedValue value, int width) => value switch
        {
            FieldValue { Pending: not null } field => (field, 0),
            BinaryValue { Op: BinOp.And, Left: var left, Right: ConstantValue mask } when width < 64 && (mask.Bits & ((1UL << width) - 1)) == (1UL << width) - 1 => Slice(left, width),
            BinaryValue { Op: BinOp.LShr, Left: FieldValue { Pending: not null } field, Right: ConstantValue shift } => (field, (int)shift.Bits),
            _ => null,
        };
        ManagedValue Visit(ManagedValue value)
        {
            if (value is ConversionValue { Kind: ConvKind.Truncate } truncate && Slice(truncate.Operand, truncate.Width) is var (field, shift)
                && field.Field.DeclaringType is DefinitionRef owner && types.Kind(owner) == TypeKind.Struct
                && types.Fields(owner).FirstOrDefault(f => f.Path[0].Equals(field.Field)) is { } whole
                && types.Project(owner, whole.Bit + shift, truncate.Width) is { Path: [var other] } overlaid && !other.Equals(field.Field)
                && overlaid.Type.Equals(truncate.Type) && evidence.Accessible(other, field.Receiver.Type))
                return new FieldValue(field.Receiver, other, truncate.Type, truncate.Width);
            return ManagedValues.Map(value, Visit);
        }
        return ManagedValues.Map(body, Visit);
    }

    /// <summary>
    /// 泛型定义的方法体取自共享实例，类型里可能还留着共享实参 object。按原生代码直接写出的访问不经过证明，
    /// 调用方有类型形参、而字段所在的类型以 object 作类型实参时不直接写出。
    /// </summary>
    internal static bool SharedArgument(MethodRef caller, params TypeRef[] types)
    {
        if (caller.Method.Owner.GenericParameters.Count == 0 && caller.Method.GenericParameters.Count == 0) return false;
        static bool Mentions(TypeRef type) => type switch
        {
            DefinitionRef d => d.Arguments.Any(a => a is DefinitionRef { Definition.FullName: "System.Object" } || Mentions(a)),
            ArrayRef a => Mentions(a.Element),
            ByRefRef r => Mentions(r.Element),
            PointerRef p => Mentions(p.Element),
            _ => false,
        };
        return types.Any(Mentions);
    }

    /// <summary>同程序集的字段按原生代码直接访问（源码由主程序集声明的放宽承接）；别的程序集的字段不能放宽。</summary>
    private ManagedValue? Unfold(ManagedValue value) => value switch
    {
        FieldValue field when field.Field.Field.Owner.Assembly == caller.Method.Owner.Assembly && !SharedArgument(caller, field.Field.DeclaringType)
            => field with { Pending = null, Unfolded = true },
        StaticFieldValue field when field.Field.Field.Owner.Assembly == caller.Method.Owner.Assembly && !SharedArgument(caller, field.Field.DeclaringType)
            => field with { Pending = null, Unfolded = true },
        _ => null,
    };

    /// <summary>未证明的访问：同程序集的字段直接写出并记录，其余的值与写入目标换成洞。</summary>
    private ManagedBody Seal(ManagedBody body)
    {
        string Reason(PendingAccess pending)
        {
            var reason = $"{pending.Reason}，也不在可证明的内联方法体中";
            if (failures.TryGetValue(pending.Address, out var failure)) reason += $"；内联证明：{failure}";
            return reason;
        }
        ManagedValue Visit(ManagedValue value)
        {
            // 写入经过的不可访问值类型字段没有证明：取不到它的地址，经过它的整个位置是洞。
            if (PendingOf(value) is null && ManagedValues.Walk(value).OfType<AddressValue>().Select(a => a.Target)
                .OfType<FieldValue>().FirstOrDefault(f => f.Pending is { Write: true } && Unfold(f) is null) is { Pending: { } through })
            {
                var throughReason = Reason(through);
                holes.Add(new RecoveryHole(through.Address, throughReason));
                return new HoleValue(throughReason, value.Type, value.Width);
            }
            if (PendingOf(value) is { } pending)
            {
                var reason = Reason(pending);
                if (Unfold(value) is { } direct)
                {
                    rules.Add(new Cpp2CS.Diagnostics.RuleTrace(UnfoldedRule, pending.Address, Cpp2CS.Diagnostics.RewriteStatus.Applied, "same-assembly", reason, null));
                    return ManagedValues.Map(direct, Visit);
                }
                holes.Add(new RecoveryHole(pending.Address, reason));
                return new HoleValue(reason, value.Type, value.Width);
            }
            return ManagedValues.Map(value, Visit);
        }
        return ManagedValues.Map(body, Visit);
    }
}
