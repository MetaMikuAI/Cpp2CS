using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>
/// 把 async 状态机的 MoveNext（Roslyn 形状）提升回入口方法，只用于 C# 输出；执行对照仍用状态机原样的 CIL。
/// 1. 状态分派按初始状态 -1 折叠；挂起分支（写状态、存 awaiter、AwaitUnsafeOnCompleted、返回）的入边改到恢复后的汇合点，挂起与恢复分支随之不可达；
/// 2. awaiter 的 GetAwaiter … GetResult 写成 <see cref="ManagedAwait"/>，IsCompleted 删去；
/// 3. builder.SetResult 写成 return，外层 catch → SetException 的模板区域与状态写入删去；
/// 4. 状态机字段换成 this、参数（入口方法写入字段的实参）与局部变量。
/// 任何一步不符合形状时返回 null 与原因，该方法保持状态机原样输出。
/// </summary>
public static partial class AsyncLifting
{
    private const string State = "<>1__state", Builder = "<>t__builder", Outer = "<>4__this";

    public static ManagedBody? Lift(ManagedBody kickoff, ManagedBody moveNext, out string reason)
    {
        var lifter = new Lifter(kickoff, moveNext);
        var body = lifter.Run();
        reason = lifter.Reason;
        return body;
    }

    /// <summary>入口方法：调用 builder.Start(ref 状态机) 的方法；返回状态机类型。</summary>
    public static TypeRef? StateMachineOf(ManagedBody kickoff) => kickoff.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>()
        .Where(c => c.Invocation.Method.Method.Name == "Start" && c.Invocation.Method.MethodArguments.Count == 1)
        .Select(c => c.Invocation.Method.MethodArguments[0]).FirstOrDefault();

    private sealed partial class Lifter(ManagedBody kickoff, ManagedBody moveNext)
    {
        private readonly Dictionary<ulong, List<ManagedStatement>> blocks = moveNext.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        private readonly List<ulong> order = moveNext.Blocks.Select(b => b.Address).ToList();
        private List<ManagedRegion> regions = moveNext.Regions.ToList();
        private readonly Dictionary<FieldDef, LocalValue> hoisted = [];

        public string Reason { get; private set; } = "";
        private bool Reject(string reason) { Reason = $"async 提升 {reason}"; return false; }
        private T? Fail<T>(string reason) where T : class { Reject(reason); return null; }
        private static bool IsThis(ManagedValue v) => v is ArgumentValue { Index: -1 };
        private static string? ThisField(ManagedValue v) => v is FieldValue f && IsThis(f.Receiver) ? f.Field.Field.Name : null;
        private static bool IsBuilder(ManagedValue? receiver) => receiver is AddressValue { Target: var target } && ThisField(target) == Builder;
        private static bool IsAwaiterField(string? name) => name?.StartsWith("<>u__", StringComparison.Ordinal) == true;
        private static ulong Mask(int width) => width is >= 64 or <= 0 ? ulong.MaxValue : (1UL << width) - 1;
        private static ulong SignExtend(ulong x, int width) => width is >= 64 or <= 0 || (x >> (width - 1) & 1) == 0 ? x : x | ~Mask(width);
        private static string? StoredField(ManagedStore store) => store.Target switch
        {
            IndirectValue { Address: AddressValue { Target: var t } } => ThisField(t),
            var t => ThisField(t),
        };

        public ManagedBody? Run()
        {
            if (kickoff.Blocks.Count == 0 || moveNext.Blocks.Count == 0) return Fail<ManagedBody>("空方法体");
            if (Holes(kickoff).Any()) return Fail<ManagedBody>("入口存在缺口，保留状态机");
            if (AsyncCaptures.Read(kickoff, out var captureReason) is not { } arguments) return Fail<ManagedBody>(captureReason);
            if (blocks.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges).Any(e => !blocks.ContainsKey(e.Target)))
                return Fail<ManagedBody>("MoveNext 控制流目标缺失");
            FoldDispatch();
            var sites = Suspensions();
            if (sites is null) return null;
            foreach (var site in sites) if (!Redirect(site.Entry, site.Join)) return null;
            if (!RemoveTemplate(sites.Count == 0)) return null;
            Prune();
            FoldDispatch();
            Simplify();
            Prune();
            FoldTaskCopies();
            foreach (var awaiter in sites.Select(s => s.Awaiter).Distinct()) if (!Await(awaiter)) return null;
            // IsCompleted 已换成常量 true：挂起判断随之折叠。
            FoldDispatch();
            Simplify();
            Prune();
            RemoveCopiedAwaiters();
            foreach (var site in sites)
                if (Uses(site.Awaiter)) return Fail<ManagedBody>($"awaiter {site.Awaiter} 仍被使用" + (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1"
                    ? "：" + string.Join(" | ", blocks.Values.SelectMany(s => s).Where(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))
                        .SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable == site.Awaiter))) : ""));
            var lifted = MapFields(arguments);
            if (Reason.Length > 0) return null;
            var body = new ManagedBody(kickoff.Method, order.Select(a => new ManagedBlock(a, lifted[a])).ToArray()) { Regions = regions };
            if (!Holes(moveNext).Order(StringComparer.Ordinal).SequenceEqual(Holes(body).Order(StringComparer.Ordinal)))
                return Fail<ManagedBody>("提升改变了 MoveNext 的缺口，保留状态机");
            return body;
        }

        private static IEnumerable<string> Holes(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements).SelectMany(s =>
            (s is ManagedHole h ? new[] { $"{h.Address:x}:{h.Terminal}:{h.Reason}" } : [])
            .Concat(ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)).SelectMany(ManagedValues.Walk).OfType<HoleValue>().Select(v => v.Reason)));

        // ---------- 1. 状态分派按初始状态折叠 ----------

        private ulong? Eval(ManagedValue v, Dictionary<Variable, ulong> known) => v switch
        {
            ConstantValue c => c.Bits & Mask(c.Width),
            LocalValue l => known.TryGetValue(l.Variable, out var x) ? x : null,
            FieldValue f when ThisField(f) == State => ulong.MaxValue & Mask(f.Width),
            ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } c => Eval(c.Operand, known) is { } x ? x & Mask(c.Width) : null,
            ConversionValue { Kind: ConvKind.SignExtend } c => Eval(c.Operand, known) is { } x ? SignExtend(x, c.Operand.Width) & Mask(c.Width) : null,
            NegatedValue n => Eval(n.Operand, known) is { } x ? x == 0 ? 1UL : 0UL : null,
            BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.And or BinOp.Or or BinOp.Xor } b => Eval(b.Left, known) is { } l && Eval(b.Right, known) is { } r
                ? b.Op switch { BinOp.Add => l + r, BinOp.Sub => l - r, BinOp.And => l & r, BinOp.Or => l | r, _ => l ^ r } & Mask(b.Width) : null,
            ComparisonValue c => Eval(c.Left, known) is { } l && Eval(c.Right, known) is { } r && Compare(c.Condition, l, r, c.Left.Width) is { } truth ? truth ? 1UL : 0UL : null,
            _ => null,
        };

        private static bool? Compare(Cond condition, ulong l, ulong r, int width)
        {
            long sl = (long)SignExtend(l, width), sr = (long)SignExtend(r, width);
            return condition switch
            {
                Cond.Eq => l == r, Cond.Ne => l != r,
                Cond.Ult => l < r, Cond.Ule => l <= r, Cond.Ugt => l > r, Cond.Uge => l >= r,
                Cond.Slt => sl < sr, Cond.Sle => sl <= sr, Cond.Sgt => sl > sr, Cond.Sge => sl >= sr,
                _ => null,
            };
        }

        /// <summary>SSA 局部变量只赋值一次：值由状态字段（初始 -1）与常量决定的分支、switch 折叠成跳转。</summary>
        private void FoldDispatch()
        {
            var known = ConstantCopies();
            var copies = new Dictionary<Variable, ulong>(known);
            var assignments = blocks.Values.SelectMany(s => s).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1).Select(g => g.Single()).ToArray();
            bool changed;
            do
            {
                changed = false;
                foreach (var a in assignments)
                    if (!known.ContainsKey(a.Target.Variable) && Eval(a.Value, known) is { } x) { known[a.Target.Variable] = x; changed = true; }
            } while (changed);
            foreach (var address in order)
            {
                var statements = blocks[address];
                for (var i = 0; i < statements.Count; i++)
                {
                    ManagedValue Value(ManagedValue value) => value is AddressValue ? value
                        : value is LocalValue local && copies.TryGetValue(local.Variable, out var constant)
                            ? new ConstantValue(constant & Mask(local.Width), local.Type, local.Width) : ManagedValues.Map(value, Value);
                    statements[i] = ManagedValues.Map(statements[i], Value, target => target) switch
                    {
                        ManagedBranch b when Eval(b.Condition, known) is { } x => new ManagedJump(b.Address, x != 0 ? b.Taken : b.Fallthrough),
                        ManagedSwitch w when Eval(w.Index, known) is { } x && x < (ulong)w.Cases.Count => new ManagedJump(w.Address, w.Cases[(int)x]),
                        var s => s,
                    };
                }
            }
        }

        // ---------- 2. 挂起点 ----------

        private sealed record Site(ulong Entry, Variable Awaiter, ManagedEdge Join);

        private Dictionary<ulong, List<ulong>> Predecessors()
        {
            var map = order.ToDictionary(a => a, _ => new List<ulong>());
            foreach (var address in order)
                foreach (var edge in blocks[address].SelectMany(ManagedValues.Edges))
                    if (map.TryGetValue(edge.Target, out var list)) list.Add(address);
            return map;
        }

        private static ulong? StateStore(IEnumerable<ManagedStatement> statements) => statements.OfType<ManagedStore>()
            .Where(s => StoredField(s) == State && s.Value is ConstantValue).Select(s => (ulong?)((ConstantValue)s.Value).Bits).FirstOrDefault();

        private List<Site>? Suspensions()
        {
            var predecessors = Predecessors();
            var sites = new List<Site>();
            foreach (var address in order)
            {
                if (blocks[address].OfType<ManagedCall>().FirstOrDefault(c => c.Invocation.Method.Method.Name is "AwaitUnsafeOnCompleted" or "AwaitOnCompleted"
                    && IsBuilder(c.Invocation.Receiver)) is not { } call) continue;
                if (call.Invocation.Arguments is not [AddressValue { Target: LocalValue awaiter }, ..]) return Fail<List<Site>>("AwaitOnCompleted 的 awaiter 不是局部变量");
                // 从调用块沿唯一前驱回溯到写入状态号的块：它是挂起分支的入口。
                var entry = address;
                var seen = new HashSet<ulong>();
                while (StateStore(blocks[entry]) is null)
                {
                    if (!seen.Add(entry) || predecessors[entry] is not [var previous] || blocks[previous].LastOrDefault() is not ManagedJump) return Fail<List<Site>>("挂起分支 没有写入状态号");
                    entry = previous;
                }
                var awaiterField = blocks[entry].Concat(blocks[address]).OfType<ManagedStore>().Select(StoredField).FirstOrDefault(IsAwaiterField)
                    ?? seen.SelectMany(a => blocks[a]).OfType<ManagedStore>().Select(StoredField).FirstOrDefault(IsAwaiterField);
                if (awaiterField is null) return Fail<List<Site>>("挂起分支 没有保存 awaiter");
                // 恢复分支：读回同一 awaiter 字段并把状态写回 -1，再跳到汇合点。
                var resume = order.FirstOrDefault(a => StateStore(blocks[a]) == 0xffffffff
                    && blocks[a].SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).Any(v => ThisField(v) == awaiterField), ulong.MaxValue);
                if (resume == ulong.MaxValue || blocks[resume].LastOrDefault() is not ManagedJump { Edge: var join }) return Fail<List<Site>>($"恢复分支 {awaiterField} 未找到");
                // 常量边复制不依赖恢复分支中的临时变量，重定向时与跳转一起保留。
                if (join.Copies.Any(c => c.Value is not ConstantValue)) return Fail<List<Site>>($"恢复分支 {awaiterField} 的边复制依赖局部值");
                sites.Add(new(entry, awaiter.Variable, join));
            }
            // 无 await 的 async 也有 builder 和完成路径；缺口或保存的恢复状态不能当作同步完成。
            if (sites.Count == 0 && (Holes(moveNext).Any()
                || blocks.Values.SelectMany(s => s).OfType<ManagedStore>().Any(s => StoredField(s) == State
                    && s.Value is not ConstantValue { Bits: 0xffffffff or 0xfffffffe })
                || blocks.Values.SelectMany(s => s).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .SelectMany(ManagedValues.Walk).Any(v => IsAwaiterField(ThisField(v)))))
                return Fail<List<Site>>("没有挂起点，但仍有缺口或恢复状态");
            return sites;
        }

        private bool Redirect(ulong entry, ManagedEdge join)
        {
            if (blocks.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges).Any(e => e.Target == entry && e.Copies.Count > 0))
                return Reject("挂起分支的入边带有复制");
            foreach (var address in order)
            {
                var statements = blocks[address];
                for (var i = 0; i < statements.Count; i++)
                    statements[i] = ManagedValues.MapEdges(statements[i], e =>
                    {
                        if (e.Target != entry) return e;
                        return join;
                    });
            }
            return true;
        }

        // ---------- 3. builder 模板 ----------

        private bool RemoveTemplate(bool synchronous)
        {
            // il2cpp 的 catch 先判定异常类型再 leave 出 handler，SetException 在 handler 之后：沿 handler 的普通出边找（不进入本区域的 try）。
            bool SetsException(ManagedRegion region)
            {
                var seen = new HashSet<ulong>();
                var pending = new Stack<ulong>([region.HandlerEntry]);
                while (pending.TryPop(out var address))
                {
                    if (region.Try.Contains(address) || !blocks.TryGetValue(address, out var statements) || !seen.Add(address) || seen.Count > 64) continue;
                    // builder.SetException 或其内联展开（runnerPromise.SetException）。
                    if (statements.OfType<ManagedCall>().Any(c => c.Invocation.Method.Method.Name == "SetException")) return true;
                    foreach (var edge in statements.SelectMany(ManagedValues.Edges)) pending.Push(edge.Target);
                }
                return false;
            }
            var template = regions.Where(r => r.Kind == ManagedRegionKind.Catch && SetsException(r)).ToArray();
            // 嵌套时取最外层（try 最大）的一个。
            if (template.Length > 1) template = [template.MaxBy(r => r.Try.Count)!];
            var completionOnly = synchronous && regions.Count == 0;
            if (template.Length != 1 && !completionOnly) return Reject($"外层 catch→SetException 区域 {template.Length} 个" + (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1"
                ? $"：区域 [{string.Join(" ", regions.Select(r => $"{r.Kind}@{r.HandlerEntry:x} try{r.Try.Count} handler{r.Handler.Count}"))}]，SetException 在 "
                  + string.Join(",", order.Where(a => blocks[a].OfType<ManagedCall>().Any(c => c.Invocation.Method.Method.Name == "SetException")).Select(a => $"{a:x}")) : ""));
            if (template.Length == 1) regions.Remove(template[0]);
            var returned = kickoff.Method.Method.ReturnType.Substitute(kickoff.Method.TypeArguments, kickoff.Method.MethodArguments);
            // 内联展开的 builder.SetResult(x)：读出 builder.runnerPromise 后按是否为 null 写 result 字段或调用 runnerPromise.SetResult(x)。
            var promiseCalls = blocks.Values.SelectMany(b => b).OfType<ManagedCall>().Where(c => c.Invocation.Method.Method.Name == "SetResult" && c.Invocation.Receiver is LocalValue)
                .GroupBy(c => ((LocalValue)c.Invocation.Receiver!).Variable).ToDictionary(g => g.Key, g => g.First());
            static bool Promise(ManagedValue v) => v is FieldValue { Field.Field.Name: "runnerPromise", Receiver: AddressValue { Target: var builder } } && ThisField(builder) == Builder;
            foreach (var address in order)
            {
                var statements = blocks[address];
                var output = new List<ManagedStatement>();
                foreach (var statement in statements)
                {
                    if (statement is ManagedAssignment { Value: var read } promise && Promise(read) && promiseCalls.TryGetValue(promise.Target.Variable, out var inlined))
                    {
                        output.Add(new ManagedReturn(promise.Address, new AsyncResultValue(inlined.Invocation.Arguments.FirstOrDefault(), returned)));
                        break;
                    }
                    if (statement is ManagedStore store && StoredField(store) == State) continue;
                    if (statement is ManagedCall { Invocation: { Method.Method.Name: "SetResult" } invocation } call && IsBuilder(invocation.Receiver))
                    {
                        output.Add(new ManagedReturn(call.Address, new AsyncResultValue(invocation.Arguments.FirstOrDefault(), returned)));
                        break;
                    }
                    output.Add(statement);
                }
                blocks[address] = output;
            }
            if (!completionOnly) return true;
            // 空方法的异常模板会被编译器省掉；只接受完成标记和常量计算，不吞掉其他逻辑。
            Prune();
            Simplify();
            var remaining = blocks.Values.SelectMany(s => s).ToArray();
            return remaining.Any(s => s is ManagedReturn { Value: AsyncResultValue }) && remaining.All(s => s switch
            {
                ManagedJump { Edge.Copies.Count: 0 } => true,
                ManagedAssignment a => Pure(a.Value),
                ManagedReturn { Value: AsyncResultValue r } => r.Value is null || Pure(r.Value),
                _ => false,
            }) || Reject("无异常模板的方法不只是同步完成");
        }

        /// <summary>删去入口不可达的块（catch 的 handler 在其 try 可达时可达）与失去 try 的区域。</summary>
        private void Prune()
        {
            var reachable = new HashSet<ulong>();
            var pending = new Stack<ulong>([order[0]]);
            while (true)
            {
                while (pending.TryPop(out var address))
                    if (blocks.ContainsKey(address) && reachable.Add(address))
                        foreach (var edge in blocks[address].SelectMany(ManagedValues.Edges)) pending.Push(edge.Target);
                var handlers = regions.Where(r => r.Try.Any(reachable.Contains) && !reachable.Contains(r.HandlerEntry)).Select(r => r.HandlerEntry).ToArray();
                if (handlers.Length == 0) break;
                foreach (var handler in handlers) pending.Push(handler);
            }
            order.RemoveAll(a => !reachable.Contains(a));
            foreach (var address in blocks.Keys.Where(a => !reachable.Contains(a)).ToArray()) blocks.Remove(address);
            regions = regions.Where(r => r.Try.Any(reachable.Contains) && reachable.Contains(r.HandlerEntry))
                .Select(r => r with { Try = r.Try.Where(reachable.Contains).ToArray(), Handler = r.Handler.Where(reachable.Contains).ToArray() }).ToList();
        }

        // ---------- 4. GetAwaiter … GetResult → await ----------

        private static bool IsAwaiter(ManagedValue? v, Variable awaiter) => v is AddressValue { Target: LocalValue l } && l.Variable == awaiter;

        private bool Await(Variable awaiter)
        {
            static ManagedValue Unwrap(ManagedValue v) => v is AddressValue a ? a.Target : v;
            // 同一个 awaiter 变量可被多个 await 点复用：awaiter 的每次构造改为把任务写入同一个新局部变量，GetResult 处 await 这个变量（按数据流，不需要配对）。
            var results = blocks.Values.SelectMany(s => s).OfType<ManagedCall>().Where(c => c.Result is not null).GroupBy(c => c.Result!.Variable)
                .Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
            var copiedTask = CopiedTask();
            ManagedValue? Task(ManagedStatement statement) => statement switch
            {
                ManagedCall { Invocation: { Method.Method.Name: "GetAwaiter" } invocation } c when c.Result?.Variable == awaiter
                    => invocation.Receiver is { } receiver ? Unwrap(receiver) : invocation.Arguments.FirstOrDefault(),
                ManagedCall { Invocation: { Method.Method.Name: ".ctor", Arguments: [var argument] } invocation } when IsAwaiter(invocation.Receiver, awaiter) => Unwrap(argument),
                ManagedAssignment { Value: NewObjectValue { Arguments: [var argument] } } a when a.Target.Variable == awaiter => Unwrap(argument),
                ManagedStore { Target: IndirectValue { Address: var target }, Value: NewObjectValue { Arguments: [var argument] } } when IsAwaiter(target, awaiter) => Unwrap(argument),
                ManagedStore { Target: IndirectValue { Address: var target }, Value: LocalValue copied } when IsAwaiter(target, awaiter)
                    && results.TryGetValue(copied.Variable, out var call) && call.Invocation.Method.Method.Name == "GetAwaiter"
                    => call.Invocation.Receiver is { } receiver ? Unwrap(receiver) : call.Invocation.Arguments.FirstOrDefault(),
                ManagedStore store when InlineTaskField(store.Target, awaiter) => store.Value,
                ManagedStore { Target: var target, Value: var value } store when StorageValue(target) is LocalValue local && local.Variable == awaiter
                    => copiedTask(value, store),
                ManagedAssignment assignment when assignment.Target.Variable == awaiter => copiedTask(assignment.Value, assignment),
                _ => null,
            };
            var tasks = order.SelectMany(a => blocks[a]).Select(Task).OfType<ManagedValue>().ToArray();
            if (tasks.Length == 0) return Reject($"awaiter {awaiter} 不是 GetAwaiter 的结果" + (Environment.GetEnvironmentVariable("CPP2CS_EMIT_DEBUG") == "1"
                ? "：" + string.Join(" | ", order.SelectMany(a => blocks[a]).Where(s => ManagedValues.Of(s).SelectMany(ManagedValues.Walk).Any(v => v is LocalValue l && l.Variable == awaiter)).Take(3)) : ""));
            if (tasks.Select(t => t.Type).Distinct().Count() != 1) return Reject($"awaiter {awaiter} 对应多种任务类型");
            var held = new LocalValue(new Variable(Storage.Temp(-2_000_000 - awaiters++), 1), tasks[0].Type, tasks[0].Width);
            FoldInlineAwaiter(awaiter, held);
            // 被复制进 awaiter 的 GetAwaiter 结果：调用删去。
            var copiedCalls = order.SelectMany(a => blocks[a]).OfType<ManagedStore>().Where(s => s is { Target: IndirectValue { Address: var target }, Value: LocalValue }
                && IsAwaiter(target, awaiter) && Task(s) is not null).Select(s => ((LocalValue)s.Value).Variable).ToHashSet();
            foreach (var address in order)
            {
                var statements = blocks[address];
                for (var i = 0; i < statements.Count; i++)
                {
                    var statement = statements[i];
                    if (statement is ManagedCall { Result: { } r } && copiedCalls.Contains(r.Variable)) { statements.RemoveAt(i--); continue; }
                    if (Task(statement) is { } task) { statements[i] = new ManagedAssignment(statement.Address, held, task); continue; }
                    switch (statement)
                    {
                        // awaiter 清零（initobj）
                        case ManagedStore { Target: IndirectValue { Address: var target }, Value: ComposedValue { Leaves.Count: 0 } } when IsAwaiter(target, awaiter):
                            statements.RemoveAt(i--);
                            break;
                        case ManagedCall { Invocation.Method.Method.Name: "get_IsCompleted" } c when IsAwaiter(c.Invocation.Receiver, awaiter):
                            // 结果只用于已经折叠的挂起判断；Simplify 删去不再使用的结果。
                            if (c.Result is null) return Reject("IsCompleted 没有结果");
                            statements[i] = new ManagedAssignment(c.Address, c.Result, new ConstantValue(1, c.Result.Type, c.Result.Width));
                            break;
                        case ManagedCall { Invocation.Method.Method.Name: "GetResult" } c when IsAwaiter(c.Invocation.Receiver, awaiter):
                            statements[i] = new ManagedAwait(c.Address, held, c.Result);
                            break;
                    }
                }
            }
            return true;
        }

        private int awaiters;

        private bool Uses(Variable variable) => blocks.Values.SelectMany(s => s).Any(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))
            .Concat(s is ManagedCall { Result: { } r } ? [r] : s is ManagedAwait { Result: { } w } ? [w] : [])
            .SelectMany(ManagedValues.Walk).Any(v => v is LocalValue l && l.Variable == variable));

        /// <summary>两边去向相同的分支改成跳转；删去结果不再使用、没有副作用的赋值（IsCompleted 的结果、状态号的副本）。</summary>
        private void Simplify()
        {
            ulong Resolve(ulong target)
            {
                var seen = new HashSet<ulong>();
                while (seen.Add(target) && blocks.TryGetValue(target, out var s) && s is [ManagedJump { Edge.Copies.Count: 0 } j]) target = j.Edge.Target;
                return target;
            }
            bool changed;
            do
            {
                changed = false;
                foreach (var address in order)
                {
                    var statements = blocks[address];
                    if (statements.LastOrDefault() is ManagedBranch { Taken.Copies.Count: 0, Fallthrough.Copies.Count: 0 } b && Resolve(b.Taken.Target) == Resolve(b.Fallthrough.Target))
                    { statements[^1] = new ManagedJump(b.Address, b.Taken); changed = true; }
                }
                var used = blocks.Values.SelectMany(s => s).SelectMany(s => ManagedValues.Of(s).Where(v => s is not ManagedAssignment a || !ReferenceEquals(v, a.Target))
                    .Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
                foreach (var statements in blocks.Values)
                {
                    changed |= statements.RemoveAll(s => s is ManagedAssignment a && !used.Contains(a.Target.Variable)
                        && (Pure(a.Value) || inlineReads.Contains(a.Target.Variable))) > 0;
                    for (var i = 0; i < statements.Count; i++)
                        statements[i] = ManagedValues.MapEdges(statements[i], edge =>
                        {
                            var copies = edge.Copies.Where(c => used.Contains(c.Target.Variable) || !Pure(c.Value)).ToArray();
                            changed |= copies.Length != edge.Copies.Count;
                            return edge with { Copies = copies };
                        });
                }
            } while (changed);
        }

        private static bool Pure(ManagedValue value) => ManagedValues.Walk(value).All(v => v is ConstantValue or LocalValue or ConversionValue or ComparisonValue
            or NegatedValue or BooleanValue or BinaryValue { Op: not (BinOp.SDiv or BinOp.UDiv or BinOp.SRem or BinOp.URem) } || v is FieldValue f && IsThis(f.Receiver) || IsThis(v));

        // ---------- 5. 状态机字段 → this、参数、局部变量 ----------

        private Dictionary<ulong, ManagedStatement[]> MapFields(IReadOnlyDictionary<FieldDef, ArgumentValue> arguments)
        {
            ManagedValue Field(FieldValue f)
            {
                var name = f.Field.Field.Name;
                if (arguments.TryGetValue(f.Field.Field, out var argument)) return argument;
                if (name is State or Builder || IsAwaiterField(name)) { Reject($"状态机字段 {name} 仍被使用"); return f; }
                if (!name.StartsWith('<') || name == Outer) { Reject($"捕获字段 {name} 没有入口赋值证据"); return f; }
                if (!hoisted.TryGetValue(f.Field.Field, out var local))
                    hoisted.Add(f.Field.Field, local = new LocalValue(new Variable(Storage.Temp(-1_000_000 - hoisted.Count), 1), f.Type, f.Width));
                return local;
            }
            ManagedValue Map(ManagedValue value) => value switch
            {
                FieldValue f when IsThis(f.Receiver) => Field(f),
                IndirectValue { Address: AddressValue { Target: FieldValue f } } when IsThis(f.Receiver) && Field(f) is LocalValue or ArgumentValue => Field(f),
                _ when IsThis(value) => UnmappedThis(value),
                _ => ManagedValues.Map(value, Map),
            };
            ManagedValue UnmappedThis(ManagedValue value) { Reject("状态机的 this 仍被使用"); return value; }
            // 外层对象（this）及其只赋值一次的副本：对它们的判空检查在 C# 里不存在（this 不为 null）。
            var outer = blocks.Values.SelectMany(s => s).OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).Where(g => g.Count() == 1)
                .Where(g => ThisField(g.Single().Value) == AsyncLifting.Outer).Select(g => g.Key).ToHashSet();
            bool IsOuter(ManagedValue v) => ThisField(v) == AsyncLifting.Outer || v is LocalValue l && outer.Contains(l.Variable);
            foreach (var statements in blocks.Values)
                statements.RemoveAll(s => s is ManagedCheck { Condition: ComparisonValue { Condition: Cond.Eq, Left: var left, Right: ConstantValue { Bits: 0 } } } && IsOuter(left));
            var output = new Dictionary<ulong, ManagedStatement[]>();
            foreach (var address in order)
                output[address] = blocks[address].Select(statement =>
                {
                    if (statement is ManagedStore store && StoredField(store) is { } name)
                    {
                        var field = (FieldValue)(store.Target is IndirectValue { Address: AddressValue { Target: var t } } ? t : store.Target);
                        if (arguments.ContainsKey(field.Field.Field)) { Reject($"写入参数字段 {name}"); return statement; }
                        if (Field(field) is LocalValue local) return new ManagedAssignment(store.Address, local, Map(store.Value));
                        return statement;
                    }
                    return ManagedValues.Map(statement, Map);
                }).ToArray();
            return output;
        }
    }
}
