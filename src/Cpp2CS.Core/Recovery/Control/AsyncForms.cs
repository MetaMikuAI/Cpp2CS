using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// async 方法还原成 Roslyn 降级后的形态，反编译器才能提升出 await。原生代码和这个形态有三处差别：
/// 构建器的 Start、Create 和等待器的 GetAwaiter、IsCompleted 被内联，写回调用并标为内联认回，执行对照按被调方法的方法体透明执行；
/// 主 try 只覆盖能抛出的块，C# 里 MoveNext 的方法体都在 try 里，没有异常边的块说明其中的调用不会抛出，并入 try 不改变行为；
/// 收尾的 SetResult 被 clang 按路径复制，合并成一个块，返回值放进局部。
/// 只有编译器降级会写出 AwaitUnsafeOnCompleted，所以它之前的分支就是 IsCompleted 的判断。形态不符时保持原样。
/// 带 try 的状态机还有两处：finally 的 if (num &lt; 0) 被 clang 算成沿路径赋值的布尔局部；try 的多个入口收拢成按序号分派。
/// 都还原成读 num，挂起和恢复时写回 num。finally 要在主 try 扩大之后还原，它的处理体在主 try 里。
/// </summary>
public static class AsyncForms
{
    private const string StateName = "<>1__state";
    private const string BuilderName = "<>t__builder";
    private const string ThisName = "<>4__this";
    private const int Budget = 64;
    /// <summary>新块的地址不对应原生代码，取高位以免与原生块和 finally 的新块重合。</summary>
    private const ulong SyntheticAddress = 5UL << 60;

    /// <param name="summary">内联证明用的方法体。</param>
    /// <param name="definition">定义的方法体，没有经过这一步。kickoff 只有在 MoveNext 也能还原时才改写：反编译器认出 kickoff 就会按 Roslyn 形态读 MoveNext，形态不符时结果是错的。</param>
    /// <param name="rejected">状态机的 MoveNext 形态不符时的原因。</param>
    public static ManagedBody Run(ManagedBody body, ManagedTypes types, Func<MethodRef, MethodRecoveryResult?> summary, Func<MethodDef, MethodRecoveryResult?> definition, out string? rejected)
    {
        rejected = null;
        if (body.Method.Method is { Name: "MoveNext", IsStatic: false } && Machine(body.Method.DeclaringType) is not null)
            return MoveNext(body, types, summary, out rejected) ?? body;
        return Kickoff(body, types, summary, definition) ?? body;
    }

    private static ManagedBody? MoveNext(ManagedBody body, ManagedTypes types, Func<MethodRef, MethodRecoveryResult?> summary, out string? rejected)
    {
        var scope = new MoveNextForm(body, types, summary);
        var scoped = scope.Prepare();
        if (scoped is null)
        {
            rejected = scope.Reason ?? "unknown";
            return null;
        }
        var form = new MoveNextForm(FinallyRecovery.Run(scoped), types, summary);
        var result = form.Complete(scope.Rewritten);
        rejected = result is null ? form.Reason ?? "unknown" : null;
        return result;
    }

    private static DefinitionRef? Machine(TypeRef type) =>
        type is DefinitionRef { Definition: { IsValueType: true } definition } machine
        && definition.Fields.Any(f => f.Name == BuilderName)
        && definition.Interfaces.OfType<DefinitionRef>().Any(i => i.Definition.FullName == "System.Runtime.CompilerServices.IAsyncStateMachine")
            ? machine : null;

    private static MethodRef? Method(DefinitionRef owner, string name, int parameters, IReadOnlyList<TypeRef>? methodArguments = null) =>
        owner.Definition.Methods.FirstOrDefault(m => m.Name == name && m.Parameters.Count == parameters && m.GenericParameters.Count == (methodArguments?.Count ?? 0)) is { } method
            ? new MethodRef(method, owner.Arguments, methodArguments ?? []) : null;

    /// <summary>没有分支的方法体摊平成语句序列。</summary>
    private static List<ManagedStatement>? Linear(ManagedBody body)
    {
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var result = new List<ManagedStatement>();
        var at = body.Blocks[0];
        for (var steps = 0; steps < Budget; steps++)
        {
            ManagedBlock? next = null;
            foreach (var statement in at.Statements)
                switch (statement)
                {
                    case ManagedJump { Edge: { Copies.Count: 0 } edge }:
                        next = blocks[edge.Target];
                        break;
                    case ManagedReturn:
                        result.Add(statement);
                        return result;
                    case ManagedJump or ManagedBranch or ManagedSwitch or ManagedThrow or ManagedRethrow or ManagedEndFault or ManagedHole:
                        return null;
                    default:
                        result.Add(statement);
                        break;
                }
            if (next is null) return null;
            at = next;
        }
        return null;
    }

    /// <summary>被调方法只是一条返回语句时返回它（常量的 IsCompleted，空的 GetResult、SetResult）。</summary>
    private static ManagedReturn? Trivial(MethodRef method, Func<MethodRef, MethodRecoveryResult?> summary) =>
        summary(method)?.Body is { Regions.Count: 0 } body && Linear(body) is [ManagedReturn only] ? only : null;

    private static bool IsLocal(ManagedValue? value, Variable variable) => value is LocalValue local && local.Variable.Equals(variable);

    /// <summary>
    /// 写成 sm.field = 参数；sm.&lt;&gt;t__builder = Create()；sm.&lt;&gt;1__state = -1；sm.&lt;&gt;t__builder.Start(ref sm)；return sm.&lt;&gt;t__builder.Task。
    /// 状态机没有初始化的字段是零，局部本来就清零。
    /// </summary>
    private static ManagedBody? Kickoff(ManagedBody body, ManagedTypes types, Func<MethodRef, MethodRecoveryResult?> summary, Func<MethodDef, MethodRecoveryResult?> definition)
    {
        if (body.Regions.Count != 0 || Linear(body) is not { } statements) return null;
        var machine = statements.OfType<ManagedCall>().Select(c => c.Invocation switch
        {
            { Method.Method.Name: "MoveNext", Receiver: AddressValue { Target: LocalValue local } } when Machine(local.Type) is not null => local,
            { Method.Method.Name: "Start", Arguments: [AddressValue { Target: LocalValue local }] } when Machine(local.Type) is not null => local,
            _ => null,
        }).OfType<LocalValue>().FirstOrDefault();
        if (machine is null) return null;
        var type = Machine(machine.Type)!;
        if (type.Definition.Methods.FirstOrDefault(m => m is { Name: "MoveNext", IsStatic: false, Parameters.Count: 0 }) is not { } moveNext
            || definition(moveNext)?.Body is not { } machineBody || MoveNext(machineBody, types, summary, out _) is null) return null;
        var builderField = new FieldRef(type.Definition.Fields.First(f => f.Name == BuilderName), type);
        if (builderField.Field.Type.Substitute(type.Arguments, []) is not DefinitionRef builderType) return null;
        var builder = new FieldValue(machine, builderField, builderType, types.ValueWidth(builderType));
        var builderAddress = new AddressValue(builder);

        var fields = new List<(FieldRef Field, ManagedValue Value)>();
        Variable? copy = null;
        ManagedCall? start = null, task = null, create = null;
        ManagedReturn? exit = null;
        foreach (var statement in statements)
            switch (statement)
            {
                case ManagedAssignment { Value: ComposedValue composed } assignment when assignment.Target.Variable.Equals(machine.Variable):
                    foreach (var (path, value) in composed.Leaves)
                    {
                        if (path is not [var field]) return null;
                        fields.Add((field, value));
                    }
                    break;
                case ManagedStore { Target: FieldValue { Receiver: var receiver, Field: var field }, Value: var value } when IsLocal(receiver, machine.Variable) || receiver is AddressValue { Target: var addressed } && IsLocal(addressed, machine.Variable):
                    fields.Add((field, value));
                    break;
                case ManagedAssignment { Value: FieldValue { Receiver: var receiver, Field.Field.Name: BuilderName } } assignment when IsLocal(receiver, machine.Variable):
                    copy = assignment.Target.Variable;
                    break;
                case ManagedCall { Invocation: { Method.Method.Name: "MoveNext" or "Start" } } call:
                    start = call;
                    break;
                case ManagedCall { Invocation: { Method.Method.Name: "get_Task" } } call:
                    task = call;
                    break;
                case ManagedCall { Invocation: { Method.Method.Name: "Create", Receiver: null } } call:
                    create = call;
                    break;
                case ManagedReturn returned:
                    exit = returned;
                    break;
                default:
                    return null;
            }
        if (start is null || exit is null) return null;
        if (task?.Invocation.Receiver is AddressValue { Target: var source }
            && !(copy is not null && IsLocal(source, copy) || source is FieldValue { Field: var read } && read.Equals(builderField))) return null;
        var state = fields.FirstOrDefault(f => f.Field.Field.Name == StateName).Value;
        if (state is null) return null;
        // 反编译器只认从参数复制的字段。
        var created = fields.FirstOrDefault(f => f.Field.Equals(builderField)).Value;
        var others = fields.Where(f => !f.Field.Equals(builderField) && f.Field.Field.Name != StateName).ToArray();
        if (others.Any(f => f.Value is not (ArgumentValue or IndirectValue { Address: ArgumentValue { Index: -1 } }))) return null;

        var next = EnumeratorForms.NextLocal(body);
        LocalValue Fresh(TypeRef local) => new(new Variable(Storage.Temp(next++), 1), local, types.ValueWidth(local));
        // 写值类型局部的字段要经它的地址。
        FieldValue Field(FieldRef field) => new(new AddressValue(machine), field, field.Field.Type.Substitute(type.Arguments, []), types.ValueWidth(field.Field.Type.Substitute(type.Arguments, [])));
        var address = start.Address;
        var result = new List<ManagedStatement>();
        foreach (var (field, value) in others) result.Add(new ManagedStore(address, Field(field), value));
        if (create is not null && (created is null || !IsLocal(created, create.Result!.Variable))) return null;
        if (Method(builderType, "Create", 0) is not { } factory) return null;
        result.Add(new ManagedStore(address, Field(builderField), new StaticCallValue(factory, builderType, types.ValueWidth(builderType), create is null)));
        result.Add(new ManagedStore(address, Field(fields.First(f => f.Field.Field.Name == StateName).Field), state));
        if (start.Invocation.Method.Method.Name == "Start") result.Add(start with { Invocation = start.Invocation with { Receiver = builderAddress } });
        else if (Method(builderType, "Start", 1, [type]) is { } starter)
            result.Add(new ManagedCall(address, new ManagedInvocation(starter, builderAddress, [new AddressValue(machine)], false), null) { Inlined = true });
        else return null;
        if (ManagedTypes.IsVoid(body.Method.Method.ReturnType))
        {
            if (task is not null) return null;
            result.Add(exit);
        }
        else if (task is not null)
        {
            if (!IsLocal(exit.Value, task.Result!.Variable)) return null;
            result.Add(task with { Invocation = task.Invocation with { Receiver = builderAddress } });
            result.Add(exit);
        }
        else
        {
            if (Method(builderType, "get_Task", 0) is not { } getter || Trivial(getter, summary) is null) return null;
            var value = Fresh(getter.Concrete(getter.Method.ReturnType));
            result.Add(new ManagedCall(address, new ManagedInvocation(getter, builderAddress, [], false), value) { Inlined = true });
            result.Add(exit with { Value = value });
        }
        return body with { Blocks = [new ManagedBlock(body.Blocks[0].Address, result)] };
    }

    private sealed class MoveNextForm(ManagedBody body, ManagedTypes types, Func<MethodRef, MethodRecoveryResult?> summary)
    {
        private readonly Dictionary<ulong, List<ManagedStatement>> code = body.Blocks.ToDictionary(b => b.Address, b => b.Statements.ToList());
        private readonly ulong entry = body.Blocks[0].Address;
        /// <summary>方法体可能已经过一轮这里的改写，新块不能和已有的同址。</summary>
        private ulong nextBlock = body.Blocks.Select(b => b.Address).Where(a => a >> 60 == SyntheticAddress >> 60).Select(a => ((a ^ SyntheticAddress) >> 40) + 1).DefaultIfEmpty(0UL).Max();
        private int nextLocal = EnumeratorForms.NextLocal(body);
        private ulong? tail;
        /// <summary>新块排在哪个原有块之后，并和它属于同样的内层区域。</summary>
        private readonly List<(ulong Block, ulong Origin)> added = [];
        public string? Reason { get; private set; }
        /// <summary>入口读状态的局部，即 Roslyn 的 num。</summary>
        private LocalValue? num;
        /// <summary>有代码按 num 的当前值判断，挂起和恢复时要写回。</summary>
        public bool Rewritten { get; private set; }

        private bool Fail(string reason)
        {
            Reason ??= reason;
            return false;
        }

        private static bool IsField(ManagedValue? value, string name) => value is FieldValue { Receiver: ArgumentValue { Index: -1 } } field && field.Field.Field.Name == name;
        private static bool IsBuilderCall(ManagedStatement statement, string name) =>
            statement is ManagedCall { Invocation: { Receiver: AddressValue { Target: var target } } invocation } && invocation.Method.Method.Name == name && IsField(target, BuilderName);
        private static bool IsAwaitCall(ManagedStatement statement) => IsBuilderCall(statement, "AwaitUnsafeOnCompleted") || IsBuilderCall(statement, "AwaitOnCompleted");
        private static long? StateStored(ManagedStatement statement) =>
            statement is ManagedStore { Target: var target, Value: ConstantValue constant } && IsField(target, StateName) ? (int)constant.Bits : null;

        private ulong Fresh() => SyntheticAddress | nextBlock++ << 40;
        private ulong FreshAfter(ulong origin)
        {
            var block = Fresh();
            added.Add((block, origin));
            return block;
        }
        private LocalValue FreshLocal(TypeRef type) => new(new Variable(Storage.Temp(nextLocal++), 1), type, types.ValueWidth(type));
        private ulong[] Predecessors(ulong target) =>
            code.Where(p => p.Value.SelectMany(ManagedValues.Edges).Any(e => e.Target == target)).Select(p => p.Key).ToArray();

        /// <summary>
        /// 把异常交给 SetException 的 catch。方法体的调用都不会抛出时 clang 删掉了它：写回一个，处理块到不了，不改变行为。
        /// </summary>
        private ManagedRegion? Main()
        {
            var main = body.Regions.Where(r => r.Kind == ManagedRegionKind.Catch && r.CatchType is null && r.Exception is { } caught
                && r.Handler.Any(a => code.TryGetValue(a, out var statements) && statements.Any(s => IsBuilderCall(s, "SetException") && s is ManagedCall { Invocation.Arguments: [var value] } && IsLocal(value, caught.Variable)))).ToArray();
            if (main is [var region]) return region;
            if (main.Length > 1)
            {
                Fail($"main-region:{main.Length}");
                return null;
            }
            if (code.Values.SelectMany(s => s).Any(s => IsBuilderCall(s, "SetException")))
            {
                Fail("main-region:other");
                return null;
            }
            var result = code.Values.SelectMany(s => s).FirstOrDefault(s => IsBuilderCall(s, "SetResult")) as ManagedCall;
            var finished = code.Values.SelectMany(s => s).FirstOrDefault(s => StateStored(s) == -2);
            if (result is null || finished is null || result.Invocation.Method.DeclaringType is not DefinitionRef builder
                || Method(builder, "SetException", 1) is not { } setException || setException.Method.Parameters[0].Type is not { } parameter)
            {
                Fail("main-region:0");
                return null;
            }
            var exception = FreshLocal(setException.Concrete(parameter));
            var handler = Fresh();
            code[handler] = [
                finished,
                new ManagedCall(result.Address, new ManagedInvocation(setException, result.Invocation.Receiver, [exception], false), null),
                new ManagedReturn(result.Address, null),
            ];
            return new ManagedRegion([], handler, [handler], exception, ManagedRegionKind.Catch);
        }

        private LocalValue? StateLocal()
        {
            var (at, index) = (entry, 0);
            for (var steps = 0; steps < Budget; steps++)
                switch (code[at].ElementAtOrDefault(index))
                {
                    case ManagedAssignment { Target: var target, Value: var value } when IsField(value, StateName): return target;
                    case ManagedAssignment { Value: var value } when IsField(value, ThisName): index++; break;
                    case ManagedJump { Edge: { Copies.Count: 0 } edge }: (at, index) = (edge.Target, 0); break;
                    default: return null;
                }
            return null;
        }

        /// <summary>finally 还原之前：去掉布尔局部，主 try 包住整个方法体。</summary>
        public ManagedBody? Prepare()
        {
            if (Main() is not { } region) return null;
            MergeChains(region);
            ForwardReturns();
            num = StateLocal();
            if (num is not null && !Flags(num)) return null;
            return Layout(region);
        }

        /// <summary>finally 还原之后：合并收尾，还原 try 的入口和 await。</summary>
        public ManagedBody? Complete(bool rewritten)
        {
            Rewritten = rewritten;
            if (Main() is not { } region) return null;
            MergeChains(region);
            ForwardReturns();
            num = StateLocal();
            if (!Tails()) return null;
            var sites = code.SelectMany(p => p.Value.Where(IsAwaitCall).Select(s => (p.Key, (ManagedCall)s))).ToArray();
            if (!Entries(sites.Select(s => s.Item2).ToArray())) return null;
            foreach (var (block, call) in sites)
                if (!Await(block, call)) return null;
            return StateReads() ? Layout(region) : null;
        }

        /// <summary>
        /// 反编译器提升后 num 没有定义，只认两处读取：方法和 try 开头的分派，finally 开头的判断。其他读取留下来就读到未赋值的局部。
        /// </summary>
        private bool StateReads()
        {
            if (num is not { } cached) return true;
            var dispatch = new HashSet<ulong>();
            foreach (var state in code.Values.SelectMany(s => s).Select(StateStored).OfType<long>().Append(-1).Distinct())
                if (state >= -1 && Dispatch(state, visited: dispatch) is null) return Fail("num:dispatch");
            var guards = body.Regions.Where(r => r.Kind == ManagedRegionKind.Finally).Select(r => r.HandlerEntry).ToHashSet();
            foreach (var (address, statements) in code)
                foreach (var statement in statements)
                {
                    var values = statement is ManagedAssignment assignment ? [assignment.Value] : ManagedValues.Of(statement);
                    if (!values.Concat(ManagedValues.CopiedValues(statement)).SelectMany(ManagedValues.Walk).Any(v => IsLocal(v, cached.Variable))) continue;
                    if (statement is not (ManagedBranch or ManagedSwitch) || !(dispatch.Contains(address) || guards.Contains(address))) return Fail("num:read");
                }
            return true;
        }

        /// <summary>值是否在测试一个布尔局部或 num 的符号位。Negated 表示值为真时测试的量为假。</summary>
        private readonly record struct BitTest(LocalValue? Flag, bool Sign, bool Negated);

        private BitTest? Bit(ManagedValue value)
        {
            switch (value)
            {
                case ComparisonValue { Condition: Cond.Ne, Right: ConstantValue { Bits: 0 } } comparison:
                    return Bit(comparison.Left);
                case ComparisonValue { Condition: Cond.Eq, Right: ConstantValue { Bits: 0 } } comparison when Bit(comparison.Left) is { } inner:
                    return inner with { Negated = !inner.Negated };
                case NegatedValue negated when Bit(negated.Operand) is { } inner:
                    return inner with { Negated = !inner.Negated };
                case ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Bitcast } conversion:
                    return Bit(conversion.Operand);
                case BinaryValue { Op: BinOp.Shl, Right: ConstantValue } shift:
                    return Bit(shift.Left);
                case BinaryValue { Op: BinOp.LShr, Left: LocalValue left, Right: ConstantValue { Bits: 31 } } when num is not null && left.Variable.Equals(num.Variable):
                    return new BitTest(null, true, false);
                case LocalValue local when num is null || !local.Variable.Equals(num.Variable):
                    return new BitTest(local, false, false);
                default:
                    return null;
            }
        }

        private static IEnumerable<(LocalValue Target, ManagedValue Value)> Definitions(ManagedStatement statement) =>
            ManagedValues.Edges(statement).SelectMany(e => e.Copies).Select(c => (c.Target, c.Value))
                .Concat(statement is ManagedAssignment assignment ? [(assignment.Target, assignment.Value)] : []);

        private const int FromEntry = 1, Suspended = 2, Resumed = 4;

        /// <summary>每个块入口处 num 可能的来历：入口的值、写过非负状态、写过负的状态。处理块取 try 里所有位置的并集。</summary>
        private Dictionary<ulong, int> StateHistory()
        {
            var before = new Dictionary<ulong, int> { [entry] = FromEntry };
            for (var changed = true; changed;)
            {
                changed = false;
                void Flow(ulong target, int state)
                {
                    if (!code.ContainsKey(target) || (before.GetValueOrDefault(target) | state) == before.GetValueOrDefault(target)) return;
                    before[target] = before.GetValueOrDefault(target) | state;
                    changed = true;
                }
                foreach (var (address, statements) in code)
                {
                    if (!before.TryGetValue(address, out var state)) continue;
                    var seen = state;
                    foreach (var statement in statements)
                    {
                        if (StateStored(statement) is { } stored) seen |= state = stored >= 0 ? Suspended : Resumed;
                        foreach (var edge in ManagedValues.Edges(statement)) Flow(edge.Target, state);
                    }
                    foreach (var region in body.Regions.Where(r => r.Try.Contains(address))) Flow(region.HandlerEntry, seen);
                }
            }
            return before;
        }

        /// <summary>
        /// 布尔局部定义按路径核对：符号位只在没写过状态的路径上有意义，常量 0 只能在写过非负状态之后，常量 1 只能在写过 -1 之后。
        /// 它们只能用作分支条件。还原后读取换成比较 num，定义删去；num 本身的其他读取必须读到入口的值。
        /// </summary>
        private bool Flags(LocalValue cached)
        {
            var statements = code.SelectMany(p => p.Value.Select(s => (Block: p.Key, Statement: s))).ToArray();
            var flags = statements.SelectMany(s => Definitions(s.Statement))
                .Where(d => Bit(d.Value) is { Sign: true, Negated: false }).Select(d => d.Target.Variable).ToHashSet();
            // 互相复制的局部是同一个量，clang 给 φ 拆出来的。
            var copies = statements.SelectMany(s => Definitions(s.Statement)).Where(d => d.Value is LocalValue).Select(d => (d.Target.Variable, Source: ((LocalValue)d.Value).Variable)).ToArray();
            for (var grown = flags.Count > 0; grown;)
            {
                grown = false;
                foreach (var (target, source) in copies)
                    if (flags.Contains(target) != flags.Contains(source))
                    {
                        flags.Add(target);
                        flags.Add(source);
                        grown = true;
                    }
            }
            var signTests = statements.Any(s => s.Statement is ManagedBranch branch && Bit(branch.Condition) is { Sign: true });
            if (flags.Count == 0 && !signTests) return true;
            var history = StateHistory();
            var nativeWrites = statements.SelectMany(s => Definitions(s.Statement)).Any(d => d.Target.Variable.Equals(cached.Variable) && !IsField(d.Value, StateName));
            foreach (var (address, list) in code)
            {
                if (!history.TryGetValue(address, out var state)) continue;
                foreach (var statement in list)
                {
                    if (StateStored(statement) is { } stored) state = stored >= 0 ? Suspended : Resumed;
                    if (statement is ManagedCall { Result: { } result } && flags.Contains(result.Variable)) return Fail("flag:call");
                    foreach (var (target, value) in Definitions(statement).Where(d => flags.Contains(d.Target.Variable)))
                    {
                        var valid = value switch
                        {
                            ConstantValue { Bits: 0 } => state == Suspended,
                            ConstantValue { Bits: 1 } => state == Resumed,
                            LocalValue local when flags.Contains(local.Variable) => true,
                            _ => Bit(value) is { Sign: true, Negated: false } && (state & FromEntry) != 0,
                        };
                        if (!valid) return Fail($"flag:definition:{state}:{value.GetType().Name}");
                    }
                    var removed = Definitions(statement).Where(d => flags.Contains(d.Target.Variable)).Select(d => d.Value).ToHashSet(ReferenceEqualityComparer.Instance);
                    var reads = statement is ManagedAssignment read ? [read.Value] : ManagedValues.Of(statement);
                    foreach (var value in reads.Concat(ManagedValues.CopiedValues(statement)).Where(v => !removed.Contains(v)))
                    {
                        if (statement is ManagedBranch condition && ReferenceEquals(value, condition.Condition) && Bit(value) is { Flag: { } tested } && flags.Contains(tested.Variable)) continue;
                        if (ManagedValues.Walk(value).Any(v => v is LocalValue l && flags.Contains(l.Variable))) return Fail("flag:read");
                        if (state != FromEntry && !nativeWrites && ManagedValues.Walk(value).Any(v => IsLocal(v, cached.Variable))) return Fail($"flag:num-read:{state}");
                    }
                }
            }
            ManagedValue Compare(bool negated) => new ComparisonValue(negated ? Cond.Sge : Cond.Slt, cached, new ConstantValue(0, cached.Type, cached.Width), types.Boolean);
            foreach (var list in code.Values)
                for (var i = list.Count - 1; i >= 0; i--)
                {
                    if (list[i] is ManagedAssignment { Target: var target } && flags.Contains(target.Variable))
                    {
                        list.RemoveAt(i);
                        continue;
                    }
                    var statement = ManagedValues.MapEdges(list[i], e => e with { Copies = e.Copies.Where(c => !flags.Contains(c.Target.Variable)).ToArray() });
                    if (statement is ManagedBranch branch && Bit(branch.Condition) is { } test && (test.Sign || test.Flag is { } flag && flags.Contains(flag.Variable)))
                        statement = branch with { Condition = Compare(test.Negated) };
                    list[i] = statement;
                }
            Rewritten = flags.Count > 0;
            return true;
        }

        /// <summary>
        /// try 开头的分派块按入口序号选择。沿入口分派走每个状态值，得到它选中的项；其余进入的边是正常入口，只能走没有被状态选中的那一项。
        /// 换成按 num 比较：恢复之后 num 是 -1，不会再选中恢复点。
        /// </summary>
        private bool Entries(IReadOnlyList<ManagedCall> sites)
        {
            var dispatchers = code.Where(p => ExceptionEntries.IsDispatch(p.Key) && p.Value is [ManagedSwitch { Index: LocalValue }]).Select(p => p.Key).ToArray();
            if (dispatchers.Length == 0 || sites.Count == 0) return true;
            if (num is not { } cached) return Fail("entries:no-state");
            var selectors = dispatchers.Select(d => ((LocalValue)((ManagedSwitch)code[d][0]).Index).Variable).ToHashSet();
            var chosen = dispatchers.ToDictionary(d => d, _ => new Dictionary<int, List<long>>());
            var used = new HashSet<ManagedEdge>(ReferenceEqualityComparer.Instance);
            var states = code.Values.SelectMany(s => s).Select(StateStored).OfType<long>().Where(k => k >= 0).Distinct().ToArray();
            var fresh = new List<(ulong Block, int Case)>();
            var freshEdges = new HashSet<ManagedEdge>(ReferenceEqualityComparer.Instance);
            if (Dispatch(-1, selectors, fresh, freshEdges) is null) return Fail("entries:dispatch");
            foreach (var state in states)
            {
                var entered = new List<(ulong Block, int Case)>();
                if (Dispatch(state, selectors, entered, used) is null) return Fail("entries:dispatch");
                foreach (var (block, selected) in entered)
                    (chosen[block].TryGetValue(selected, out var list) ? list : chosen[block][selected] = []).Add(state);
            }
            // 新进入方法时走过的边也是正常入口。
            used.ExceptWith(freshEdges);
            var kept = new HashSet<Variable>();
            foreach (var dispatcher in dispatchers)
            {
                var table = (ManagedSwitch)code[dispatcher][0];
                var selector = ((LocalValue)table.Index).Variable;
                var normal = fresh.Where(f => f.Block == dispatcher).Select(f => f.Case).ToHashSet();
                foreach (var edge in code.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges).Where(e => e.Target == dispatcher && !used.Contains(e)))
                {
                    if (edge.Copies.FirstOrDefault(c => c.Target.Variable.Equals(selector)) is not { Value: ConstantValue { } selected }) return Fail("entries:selector");
                    normal.Add((int)selected.Bits);
                }
                var cases = chosen[dispatcher];
                // 状态值按 num 选择。正常入口只有一个时直接跳过去，有几个时仍按序号选。
                ManagedStatement otherwise;
                if (normal.Count > 1)
                {
                    otherwise = table;
                    kept.Add(selector);
                }
                else
                {
                    var target = normal.Count == 1 ? normal.Single() : cases.Count > 0 ? cases.Keys.Max() : -1;
                    if (target < 0) return Fail("entries:empty");
                    if (normal.Count == 0) cases.Remove(target);
                    otherwise = new ManagedJump(table.Address, new ManagedEdge(table.Cases[target].Target, []));
                }
                var tests = cases.SelectMany(c => c.Value.Select(k => (State: k, Case: c.Key))).ToArray();
                var at = dispatcher;
                foreach (var (state, selected) in tests)
                {
                    var next = FreshAfter(at);
                    var test = new ComparisonValue(Cond.Eq, cached, new ConstantValue((ulong)(uint)(int)state, cached.Type, cached.Width), types.Boolean);
                    code[at] = [new ManagedBranch(table.Address, test, new ManagedEdge(table.Cases[selected].Target, []), new ManagedEdge(next, []))];
                    at = next;
                }
                code[at] = [otherwise];
            }
            foreach (var list in code.Values)
                for (var i = 0; i < list.Count; i++)
                    list[i] = ManagedValues.MapEdges(list[i], e => e with { Copies = e.Copies.Where(c => !selectors.Contains(c.Target.Variable) || kept.Contains(c.Target.Variable) && !used.Contains(e)).ToArray() });
            Rewritten = true;
            return true;
        }

        /// <summary>只有一个前驱的后继并入前驱，下面的匹配不必考虑语句被空块隔开。不跨内层区域的边界。</summary>
        private void MergeChains(ManagedRegion main)
        {
            var inner = body.Regions.Where(r => !ReferenceEquals(r, main)).ToArray();
            string Place(ulong block) => string.Join(",", inner.Select((r, i) => r.Try.Contains(block) ? $"t{i}" : r.Handler.Contains(block) ? $"h{i}" : "")) + (main.Handler.Contains(block) ? "m" : "");
            var entries = body.Regions.Select(r => r.HandlerEntry).ToHashSet();
            var predecessors = new Dictionary<ulong, int>();
            foreach (var edge in code.Values.SelectMany(s => s).SelectMany(ManagedValues.Edges))
                predecessors[edge.Target] = predecessors.GetValueOrDefault(edge.Target) + 1;
            foreach (var address in body.Blocks.Select(b => b.Address))
            {
                if (!code.TryGetValue(address, out var statements)) continue;
                while (statements is [.., ManagedJump { Edge: { Copies.Count: 0 } edge }] && edge.Target != address && edge.Target != entry
                    && predecessors.GetValueOrDefault(edge.Target) == 1 && !entries.Contains(edge.Target) && Place(address) == Place(edge.Target))
                {
                    statements.RemoveAt(statements.Count - 1);
                    statements.AddRange(code[edge.Target]);
                    code.Remove(edge.Target);
                }
            }
        }

        /// <summary>跳到只有 return 的块直接写成 return：处理块和 try 可能共用这个块。</summary>
        private void ForwardReturns()
        {
            foreach (var statements in code.Values)
                if (statements is [.., ManagedJump { Edge: { Copies.Count: 0 } edge } jump] && code[edge.Target] is [ManagedReturn { Value: null }])
                    statements[^1] = new ManagedReturn(jump.Address, null);
        }

        /// <summary>state = -2；清理字段；SetResult；return。clang 可能按路径复制，都合并到一个块，返回值经局部传入。</summary>
        private bool Tails()
        {
            var calls = code.SelectMany(p => p.Value.Where(s => IsBuilderCall(s, "SetResult")).Select(s => (Block: p.Key, Call: (ManagedCall)s))).ToArray();
            if (calls.Length == 0) return true;
            List<ManagedStatement>? canonical = null;
            LocalValue? result = null;
            var starts = new List<(ulong Block, int Index, ManagedValue? Value)>();
            foreach (var (block, call) in calls)
            {
                if (!Returns(block, code[block].IndexOf(call) + 1)) return Fail("tail:after");
                var cleanups = new List<ManagedStatement>();
                var (at, index) = (block, code[block].IndexOf(call));
                ManagedStatement? state = null;
                for (var steps = 0; steps < Budget && state is null; steps++)
                {
                    if (index > 0)
                    {
                        var statement = code[at][--index];
                        if (StateStored(statement) == -2) state = statement;
                        else if (statement is ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } }) cleanups.Insert(0, statement);
                        else return Fail($"tail:before:{statement.GetType().Name}");
                        continue;
                    }
                    if (Predecessors(at) is not [var previous] || code[previous] is not [.., ManagedJump { Edge.Copies.Count: 0 }]) return Fail("tail:join");
                    (at, index) = (previous, code[previous].Count - 1);
                }
                if (state is null) return Fail("tail:state");
                if (call.Invocation.Arguments.Count > 1) return Fail("tail:arguments");
                var value = call.Invocation.Arguments.FirstOrDefault();
                // 返回值在清理之前求值。
                if (value is not null && cleanups.OfType<ManagedStore>().Any(c => ManagedValues.Walk(value).Any(v => ManagedStructure.Value(v, c.Target)))) return Fail("tail:cleanup-read");
                var list = cleanups.Prepend(state).Append(call).Append(new ManagedReturn(call.Address, null)).ToList();
                if (canonical is null) canonical = list;
                else if (canonical.Count != list.Count || !canonical.Zip(list).Take(list.Count - 2)
                    .All(p => p.First is ManagedStore a && p.Second is ManagedStore b && ManagedStructure.Value(a.Target, b.Target) && ManagedStructure.Value(a.Value, b.Value))) return Fail("tail:differ");
                starts.Add((at, index, value));
            }
            var address = Fresh();
            if (starts[0].Value is { } first) result = FreshLocal(first.Type);
            var setResult = (ManagedCall)canonical![^2];
            canonical[^2] = setResult with { Invocation = setResult.Invocation with { Arguments = result is null ? [] : [result] } };
            foreach (var (block, index, value) in starts)
            {
                var statements = code[block];
                var at = statements[index].Address;
                statements.RemoveRange(index, statements.Count - index);
                statements.Add(new ManagedJump(at, new ManagedEdge(address, result is null ? [] : [new ManagedCopy(result, value!)])));
            }
            code[address] = canonical;
            tail = address;
            return true;
        }

        private bool Returns(ulong block, int index)
        {
            for (var steps = 0; steps < Budget; steps++)
                switch (code[block].ElementAtOrDefault(index))
                {
                    case ManagedReturn { Value: null }: return true;
                    case ManagedJump { Edge: { Copies.Count: 0 } edge }: (block, index) = (edge.Target, 0); break;
                    default: return false;
                }
            return false;
        }

        private static long? Evaluate(ManagedValue value, HashSet<Variable> state, long known) =>
            ConstantConditions.Evaluate(value, leaf => leaf is LocalValue local && state.Contains(local.Variable) || IsField(leaf, StateName) ? known : null);

        /// <summary>
        /// 按状态值走入口的分派，停在第一条不是分派的语句。selectors 是 try 入口的序号局部：
        /// 走过的边写入序号，分派块按序号选择，选择记到 entered，经过的边记到 used。
        /// </summary>
        private (ulong Block, int Index)? Dispatch(long known, HashSet<Variable>? selectors = null, List<(ulong Block, int Case)>? entered = null, HashSet<ManagedEdge>? used = null, HashSet<ulong>? visited = null)
        {
            var state = new HashSet<Variable>();
            var selected = new Dictionary<Variable, int>();
            var (at, index) = (entry, 0);
            bool Passes(ManagedEdge edge) => edge.Copies.All(c => selectors is not null && selectors.Contains(c.Target.Variable) && c.Value is ConstantValue);
            void Take(ManagedEdge edge)
            {
                foreach (var copy in edge.Copies) selected[copy.Target.Variable] = (int)((ConstantValue)copy.Value).Bits;
                if (edge.Copies.Count > 0) used?.Add(edge);
                (at, index) = (edge.Target, 0);
            }
            for (var steps = 0; steps < Budget; steps++)
            {
                if (index >= code[at].Count) return null;
                visited?.Add(at);
                switch (code[at][index])
                {
                    case ManagedAssignment { Target: var target, Value: var value } when IsField(value, StateName):
                        state.Add(target.Variable);
                        index++;
                        break;
                    case ManagedAssignment { Value: var value } when IsField(value, ThisName):
                        index++;
                        break;
                    case ManagedJump { Edge: var edge } when Passes(edge):
                        Take(edge);
                        break;
                    case ManagedBranch branch when Evaluate(branch.Condition, state, known) is { } taken && Passes(taken != 0 ? branch.Taken : branch.Fallthrough):
                        Take(taken != 0 ? branch.Taken : branch.Fallthrough);
                        break;
                    case ManagedSwitch { Index: LocalValue selector } choice when selected.TryGetValue(selector.Variable, out var chosen) && chosen >= 0 && chosen < choice.Cases.Count && Passes(choice.Cases[chosen]):
                        entered?.Add((at, chosen));
                        Take(choice.Cases[chosen]);
                        break;
                    case ManagedSwitch choice when Evaluate(choice.Index, state, known) is { } value && value >= 0 && value < choice.Cases.Count && Passes(choice.Cases[(int)value]):
                        Take(choice.Cases[(int)value]);
                        break;
                    default:
                        return (at, index);
                }
            }
            return null;
        }

        private ulong Settle(ulong block)
        {
            for (var steps = 0; steps < Budget && code[block] is [ManagedJump { Edge: { Copies.Count: 0 } edge }]; steps++) block = edge.Target;
            return block;
        }

        /// <summary>
        /// awaiter = X.GetAwaiter()；if (awaiter.IsCompleted) goto 完成；state = k；u = awaiter；AwaitUnsafeOnCompleted；return；
        /// 恢复：awaiter = u；u = default；state = -1；完成：awaiter.GetResult()。
        /// </summary>
        private bool Await(ulong block, ManagedCall call)
        {
            if (call.Invocation.Arguments is not [AddressValue { Target: LocalValue passed }, ArgumentValue { Index: -1 } machine]
                || call.Invocation.Method.MethodArguments is not [DefinitionRef { Definition.IsValueType: true } awaiterType, ..]) return Fail("await:shape");
            var index = code[block].IndexOf(call);
            if (!Returns(block, index + 1)) return Fail("await:after");
            // 挂起段：状态、保存等待器、传给 Await 的副本。
            ManagedStatement? stateStore = null;
            FieldValue? field = null;
            ManagedValue? value = null;
            var (at, start) = (block, index);
            for (var steps = 0; steps < Budget; steps++)
            {
                if (start > 0)
                {
                    var statement = code[at][start - 1];
                    if (StateStored(statement) is not null) stateStore = statement;
                    else if (statement is ManagedStore { Target: FieldValue target, Value: var saved } && target.Field.Field.Name.StartsWith("<>u__", StringComparison.Ordinal)) (field, value) = (target, saved);
                    else if (statement is ManagedAssignment assignment && assignment.Target.Variable.Equals(passed.Variable)) value ??= assignment.Value;
                    else break;
                    start--;
                    continue;
                }
                if (stateStore is not null && field is not null) break;
                if (Predecessors(at) is not [var previous] || code[previous] is not [.., ManagedJump { Edge.Copies.Count: 0 }]) break;
                (at, start) = (previous, code[previous].Count - 1);
            }
            if (stateStore is null || field is null || value is null) return Fail($"await:group:{stateStore is null}:{field is null}");
            // 恢复段。
            if (Dispatch(StateStored(stateStore)!.Value) is not var (resume, resumeIndex)) return Fail("await:dispatch");
            LocalValue? loaded = null;
            ManagedStatement? reset = null, restored = null;
            var (cursor, position) = (resume, resumeIndex);
            ulong? completed = null;
            for (var steps = 0; steps < Budget && completed is null; steps++)
            {
                var statement = code[cursor].ElementAtOrDefault(position);
                switch (statement)
                {
                    case ManagedAssignment { Target: var target, Value: var read } when ManagedStructure.Value(read, field):
                        loaded = target;
                        position++;
                        break;
                    case ManagedStore { Target: var written } when ManagedStructure.Value(written, field):
                        reset = statement;
                        position++;
                        break;
                    case not null when StateStored(statement) == -1:
                        restored = statement;
                        position++;
                        break;
                    case ManagedJump { Edge: { Copies.Count: 0 } edge } when restored is null || reset is null:
                        (cursor, position) = (edge.Target, 0);
                        break;
                    case ManagedJump { Edge: { Copies.Count: 0 } edge }:
                        completed = edge.Target;
                        break;
                    case null:
                        return Fail("await:resume-end");
                    default:
                        // 恢复段之后的代码和恢复段在一个块里，完成路径不经过这里。
                        if (restored is null) return Fail($"await:resume:{statement.GetType().Name}");
                        var rest = FreshAfter(cursor);
                        code[rest] = code[cursor].Skip(position).ToList();
                        code[cursor].RemoveRange(position, code[cursor].Count - position);
                        completed = rest;
                        break;
                }
            }
            if (completed is not { } continuation || restored is null) return Fail("await:resume");
            var awaiter = loaded ?? FreshLocal(awaiterType);
            reset ??= new ManagedStore(restored.Address, field, new ComposedValue(awaiterType, []));

            // 判断段。
            if (!Check(at, start, value, awaiter, awaiterType, continuation, out var suspend)) return false;
            if (!Completion(continuation, awaiter, awaiterType)) return false;
            var state = StateStored(stateStore)!.Value;
            var suspended = new List<ManagedStatement>();
            if (Rewritten && num is { } cached) suspended.Add(new ManagedAssignment(stateStore.Address, cached, new ConstantValue((ulong)(uint)(int)state, cached.Type, cached.Width)));
            suspended.AddRange([
                stateStore,
                new ManagedStore(call.Address, field, awaiter),
                call with { Invocation = call.Invocation with { Arguments = [new AddressValue(awaiter), machine] } },
                new ManagedReturn(call.Address, null),
            ]);
            code[suspend] = suspended;
            var resumed = code[resume];
            resumed.RemoveRange(resumeIndex, resumed.Count - resumeIndex);
            resumed.Add(new ManagedAssignment(restored.Address, awaiter, field));
            resumed.Add(reset);
            if (Rewritten && num is { } current) resumed.Add(new ManagedAssignment(restored.Address, current, new ConstantValue(uint.MaxValue, current.Type, current.Width)));
            resumed.Add(restored);
            resumed.Add(new ManagedJump(restored.Address, new ManagedEdge(continuation, [])));
            return true;
        }

        /// <summary>重写挂起段之前的判断，返回挂起段的新块。</summary>
        private bool Check(ulong block, int index, ManagedValue value, LocalValue awaiter, DefinitionRef awaiterType, ulong continuation, out ulong suspend)
        {
            suspend = FreshAfter(block);
            if (Method(awaiterType, "get_IsCompleted", 0) is not { } isCompleted) return Fail("check:no-is-completed");
            var completedFlag = FreshLocal(isCompleted.Concrete(isCompleted.Method.ReturnType));
            ulong owner;
            List<ManagedStatement> before;
            ManagedEdge completedEdge = new(continuation, []), pendingEdge = new(suspend, []);
            var inlined = true;
            if (index == 0 && Predecessors(block) is [var previous] && code[previous] is [.., ManagedBranch branch])
            {
                owner = previous;
                before = code[owner];
                before.RemoveAt(before.Count - 1);
                var (flag, completedOnTaken) = branch.Condition switch
                {
                    LocalValue local => (local, true),
                    NegatedValue { Operand: LocalValue local } => (local, false),
                    ComparisonValue { Condition: Cond.Ne, Left: LocalValue local, Right: ConstantValue { Bits: 0 } } => (local, true),
                    ComparisonValue { Condition: Cond.Eq, Left: LocalValue local, Right: ConstantValue { Bits: 0 } } => (local, false),
                    _ => (null, false),
                };
                if (flag is null) return Fail($"check:condition:{branch.Condition.GetType().Name}");
                var definition = before.FindLastIndex(s => s is ManagedCall c && IsLocal(c.Result, flag.Variable));
                if (definition < 0) return Fail("check:test-not-in-block");
                if (definition != before.Count - 1) return Fail($"check:test-not-last:{before[^1].GetType().Name}");
                var test = (ManagedCall)before[definition];
                if (!IsTest(test)) return Fail($"check:test:{test.Invocation.Method.Method.Name}");
                if (ReadElsewhere(flag.Variable, branch)) return Fail("check:flag-read");
                var (completedSide, pendingSide) = completedOnTaken ? (branch.Taken, branch.Fallthrough) : (branch.Fallthrough, branch.Taken);
                if (Settle(pendingSide.Target) != Settle(block)) return Fail("check:pending-target");
                if (Settle(completedSide.Target) != Settle(continuation)) return Fail("check:completed-target");
                // Status 读的就是等待的值；IsCompleted 没有内联时保持原生调用。
                if (test.Invocation.Method.Method.Name == "get_Status"
                    && !(value is NewObjectValue { Arguments: [var awaited] } && ManagedStructure.Value(awaited, test.Invocation.Receiver))) return Fail("check:status-receiver");
                inlined = test.Invocation.Method.Method.Name != "get_IsCompleted" || test.Inlined;
                before.RemoveAt(definition);
                completedEdge = new ManagedEdge(continuation, completedSide.Copies.Where(c => !c.Target.Variable.Equals(awaiter.Variable)).ToArray());
                pendingEdge = new ManagedEdge(suspend, pendingSide.Copies.Where(c => !c.Target.Variable.Equals(awaiter.Variable)).ToArray());
            }
            else
            {
                // IsCompleted 是常量 false，内联后没有分支。
                if (Trivial(isCompleted, summary) is not { Value: ConstantValue { Bits: 0 } }) return Fail($"check:no-branch:{index}:{Predecessors(block).Length}");
                if (index > 0)
                {
                    owner = block;
                    before = code[owner];
                    before.RemoveRange(index, before.Count - index);
                }
                else
                {
                    if (Predecessors(block) is not [var only] || code[only] is not [.., ManagedJump { Edge.Copies.Count: 0 }]) return Fail("check:no-branch-join");
                    owner = only;
                    before = code[owner];
                    before.RemoveAt(before.Count - 1);
                }
            }
            var at = before.Count > 0 ? before[^1].Address : block;
            if (!Acquire(before, value, awaiter, at)) return false;
            before.Add(new ManagedCall(at, new ManagedInvocation(isCompleted, new AddressValue(awaiter), [], false), completedFlag) { Inlined = inlined });
            before.Add(new ManagedBranch(at, completedFlag, completedEdge, pendingEdge));
            return true;
        }

        /// <summary>IsCompleted 内联后留下的判断：直接调用 IsCompleted，或读 UniTask.Status。</summary>
        private static bool IsTest(ManagedCall call) =>
            call.Invocation.Method.Method.Name is "get_IsCompleted" or "get_Status" && call.Invocation.Arguments.Count == 0;

        private bool ReadElsewhere(Variable variable, ManagedStatement except) =>
            code.Values.SelectMany(s => s).Where(s => !ReferenceEquals(s, except))
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk).Any(v => IsLocal(v, variable));

        /// <summary>取得等待器：内联的 new Awaiter(in X) 写回 X.GetAwaiter()，已有调用就改写结果局部。</summary>
        private bool Acquire(List<ManagedStatement> before, ManagedValue value, LocalValue awaiter, ulong at)
        {
            if (value is LocalValue local)
            {
                var definition = before.FindLastIndex(s => s switch
                {
                    ManagedCall call => IsLocal(call.Result, local.Variable),
                    ManagedAssignment assignment => assignment.Target.Variable.Equals(local.Variable),
                    _ => false,
                });
                if (definition < 0) return local.Variable.Equals(awaiter.Variable) || Fail("acquire:no-definition");
                switch (before[definition])
                {
                    case ManagedCall call when definition == before.Count - 1:
                        before[definition] = call with { Result = awaiter };
                        return true;
                    case ManagedAssignment assignment:
                        before.RemoveAt(definition);
                        value = assignment.Value;
                        break;
                    default:
                        return Fail($"acquire:definition:{before[definition].GetType().Name}");
                }
            }
            if (value is not NewObjectValue { Transparent: true, Arguments: [AddressValue { Target: var awaitable }], Constructor.DeclaringType: var constructed }) return Fail($"acquire:value:{value.GetType().Name}");
            if (awaitable.Type is not DefinitionRef owner || Method(owner, "GetAwaiter", 0) is not { } getter || !getter.Concrete(getter.Method.ReturnType).Equals(constructed)) return Fail("acquire:no-get-awaiter");
            before.Add(new ManagedCall(at, new ManagedInvocation(getter, new AddressValue(awaitable), [], false), awaiter) { Inlined = true });
            return true;
        }

        /// <summary>完成路径从 GetResult 开始；空的 GetResult 被内联掉了，写回来。</summary>
        private bool Completion(ulong continuation, LocalValue awaiter, DefinitionRef awaiterType)
        {
            var at = Settle(continuation);
            if (code[at].FirstOrDefault() is ManagedCall { Invocation: { Method.Method.Name: "GetResult", Receiver: AddressValue { Target: var receiver } } } && IsLocal(receiver, awaiter.Variable)) return true;
            if (Method(awaiterType, "GetResult", 0) is not { } getResult || Trivial(getResult, summary) is not { Value: null }) return Fail($"completion:{code[at].FirstOrDefault()?.GetType().Name}");
            code[at].Insert(0, new ManagedCall(at, new ManagedInvocation(getResult, new AddressValue(awaiter), [], false), null) { Inlined = true });
            return true;
        }

        /// <summary>入口只留读状态和 this；其余都进 try；try、处理块、收尾依次排列。</summary>
        private ManagedBody? Layout(ManagedRegion main)
        {
            if (Predecessors(entry).Length != 0)
            {
                Fail("layout:entry-loop");
                return null;
            }
            // 入口可能是一串空块，读状态和 this 的语句在后面。
            var kept = new List<ManagedStatement>();
            var (first, index) = (entry, 0);
            for (var steps = 0; steps < Budget; steps++)
            {
                var statement = code[first].ElementAtOrDefault(index);
                if (statement is ManagedAssignment { Value: var value } && (IsField(value, StateName) || IsField(value, ThisName)))
                {
                    kept.Add(statement);
                    index++;
                }
                else if (statement is ManagedJump { Edge: { Copies.Count: 0 } edge } && edge.Target != tail && Predecessors(edge.Target).Length == 1) (first, index) = (edge.Target, 0);
                else break;
            }
            // 读状态的语句后面不再有别的语句时，try 从那个块开始，它可以是内层 try 的第一个块。
            var head = first;
            if (first == entry || index > 0)
            {
                head = Fresh();
                code[head] = code[first].Skip(index).ToList();
            }
            var address = code[head].FirstOrDefault()?.Address ?? entry;
            code[entry] = [.. kept, new ManagedJump(address, new ManagedEdge(head, []))];

            // 内层 try 的入口可能就是方法入口：它从读状态之后开始，读字段不会抛出。
            var handler = main.Handler.ToHashSet();
            if (handler.Contains(entry) || body.Regions.Any(r => !ReferenceEquals(r, main) && (r.Handler.Contains(entry) || r.Handler.Contains(first))))
            {
                Fail("layout:entry-region");
                return null;
            }
            // state = -2 开始收尾，从这里分开。方法体只有收尾时 try 是空的。
            foreach (var at in code.Keys.ToArray())
            {
                var finish = code[at].FindIndex(s => StateStored(s) == -2);
                if (handler.Contains(at) || finish < 0 || finish == 0 && at != head) continue;
                var rest = FreshAfter(at);
                code[rest] = code[at].Skip(finish).ToList();
                code[at] = [.. code[at].Take(finish), new ManagedJump(code[rest][0].Address, new ManagedEdge(rest, []))];
            }
            IEnumerable<ulong> Moved(IEnumerable<ulong> list) => list.Select(a => a == first ? head : a).Where(a => a != entry);
            var inner = body.Regions.Where(r => !ReferenceEquals(r, main)).ToArray();
            var inTry = new HashSet<ulong>();
            var work = new Stack<ulong>();
            work.Push(head);
            // 主 try 到 state = -2 为止，后面的收尾在 try 外。
            var finishing = new HashSet<ulong>();
            while (work.TryPop(out var at))
            {
                if (handler.Contains(at))
                {
                    Fail("layout:into-handler");
                    return null;
                }
                if (at == tail || code[at].Any(s => StateStored(s) == -2))
                {
                    finishing.Add(at);
                    continue;
                }
                if (!inTry.Add(at)) continue;
                foreach (var edge in code[at].SelectMany(ManagedValues.Edges)) work.Push(edge.Target);
                foreach (var region in inner.Where(r => r.Try.Contains(at))) work.Push(region.HandlerEntry);
                foreach (var region in inner.Where(r => r.Handler.Contains(at)))
                    // 内层 catch 的处理块是落地块支配的块，可能把主 catch 也算进去。
                    foreach (var member in region.Handler.Where(a => code.ContainsKey(a) && !handler.Contains(a))) work.Push(member);
            }
            // 原来不在 try 里的块并入时不能显式抛出；在内层 try 里的块，异常先到内层的处理块。
            var previous = main.Try.ToHashSet();
            var entered = previous.Contains(first);
            foreach (var at in inTry)
                if (!(previous.Contains(at) || at == head && entered || inner.Any(r => r.Try.Contains(at))) && code[at].Any(s => s is ManagedThrow or ManagedRethrow or ManagedCheck or ManagedHole))
                {
                    Fail($"layout:throws:{code[at].First(s => s is ManagedThrow or ManagedRethrow or ManagedCheck or ManagedHole).GetType().Name}");
                    return null;
                }

            // 新块跟在来源之后；来源可能已不可达，这里按原有块序定位。
            var followers = added.ToLookup(a => a.Origin, a => a.Block);
            IEnumerable<ulong> Placed(ulong block) => followers[block].SelectMany(Placed).Prepend(block);
            var placed = Placed(head).Concat(body.Blocks.Select(b => b.Address).Where(a => a != head).SelectMany(Placed)).ToArray();
            var order = placed.Where(a => a != entry && inTry.Contains(a)).ToList();
            var layout = new List<ulong> { entry };
            layout.AddRange(order);
            layout.AddRange(main.Handler.Where(code.ContainsKey));
            // 收尾的块可能还连着别的块，新块跟在来源之后。
            var outside = new HashSet<ulong>();
            work = new Stack<ulong>(finishing);
            while (work.TryPop(out var at))
                if (outside.Add(at))
                    foreach (var edge in code[at].SelectMany(ManagedValues.Edges).Where(e => !inTry.Contains(e.Target) && !handler.Contains(e.Target))) work.Push(edge.Target);
            layout.AddRange(placed.Where(outside.Contains));
            if (tail is { } end && !layout.Contains(end)) layout.Add(end);
            var written = layout.ToHashSet();
            var regions = body.Regions.Where(r => !ReferenceEquals(r, main))
                .Select(r => r with { Try = Moved(r.Try).SelectMany(Placed).Where(written.Contains).ToArray(), Handler = r.Handler.Where(a => !handler.Contains(a)).SelectMany(Placed).Where(written.Contains).ToArray() })
                .Where(r => r.Try.Count > 0 && r.Handler.Contains(r.HandlerEntry))
                .Append(main with { Try = order, Handler = main.Handler.Where(written.Contains).ToArray() }).ToArray();
            return body with { Blocks = layout.Select(a => new ManagedBlock(a, code[a])).ToArray(), Regions = regions };
        }
    }
}
