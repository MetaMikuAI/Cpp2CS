using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>
/// 内联方法的认回（F9 单字段访问器的推广，F6 的前置）：clang 把库类型的小方法（UniTask.Awaiter.IsCompleted、GetResult、
/// AsyncUniTaskMethodBuilder.SetResult、SetException……）整段内联进调用者，恢复出的调用者因此直接读写这些类型的私有字段，
/// 既写不成可验证的 IL，ILSpy 也还原不出 await。这里在调用者的方法体里找出与被调方法体等价的区域，换成一次调用。
///
/// 匹配不比较控制流的形状（内联后会发生跳转穿透、返回值并入调用者的分支），而比较可观察事件：
/// 从区域起点开始，调用者与被调方法在同一组随机取值下同步执行，依次产生的调用、写入、检查必须逐个相同；
/// 被调方法返回之后，调用者只能经过纯计算与分支到达区域出口，出口按返回值区分（void 一个出口，bool 两个出口）。
/// 叶子（字段读取、调用结果、区域外的局部变量与参数）在两侧按同一结构取同一个随机值；被调方法的参数由字段链的结构统一得到。
///
/// 这一步只是候选：认回的调用在执行对照中按被调方法自身（已独立 verified 的）方法体透明执行，整个调用者仍由执行对照判定。
/// </summary>
public static class InlineRecognition
{
    /// <summary>可认回的被调方法：恢复出的无洞方法体，不含异常区域。</summary>
    public sealed record Callee(MethodRef Method, ManagedBody Body, bool ReturnsBool)
    {
        /// <summary>匹配用的方法体：参数编号平移 <see cref="Shift"/>，与调用者自己的参数区分开（调用者的 this 也是 ArgumentValue(-1)）。</summary>
        public ManagedBody Pattern { get; } = ManagedValues.Map(Body, v => Substitute(v, x => x is ArgumentValue a ? a with { Index = a.Index - Shift } : null));

        /// <summary>方法体读写的字段：区域起点的越权字段须在其中（预筛，避免对每个候选都同步执行一遍）。</summary>
        public HashSet<FieldRef> Fields { get; } = Body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
            .OfType<FieldValue>().Select(f => f.Field).ToHashSet();
    }

    private const int Shift = 1000;

    private static bool IsParameter(ManagedValue value) => value is ArgumentValue { Index: <= -Shift + 64 };

    private const int Runs = 48;
    private static readonly bool Debug = Environment.GetEnvironmentVariable("CPP2CS_INLINE_DEBUG") == "1";

    private static void Trace(string message)
    {
        if (Debug) Console.Error.WriteLine($"  [内联] {message}");
    }
    private const int StepLimit = 400;

    /// <summary>反复认回直到不动点；返回改写后的方法体（没有认回时返回原对象）。</summary>
    public static ManagedBody Rewrite(ManagedBody caller, IReadOnlyList<Callee> callees, TypeRef boolean, Func<ManagedValue, bool> anchor)
    {
        var next = -200000;
        for (var round = 0; round < 64; round++)
        {
            var rewritten = RewriteOnce(caller, callees, boolean, anchor, ref next);
            if (rewritten is null) return caller;
            caller = rewritten;
        }
        return caller;
    }

    private static ManagedBody? RewriteOnce(ManagedBody caller, IReadOnlyList<Callee> callees, TypeRef boolean, Func<ManagedValue, bool> anchor, ref int next)
    {
        var blocks = caller.Blocks.ToDictionary(b => b.Address);
        foreach (var block in caller.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                var statement = block.Statements[i];
                if (statement is ManagedCall { Inlined: true }) continue;
                var anchored = ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).Where(anchor).OfType<FieldValue>().Select(f => f.Field).ToHashSet();
                var call = statement as ManagedCall;
                foreach (var callee in callees)
                {
                    // 起点：语句读到被调方法也读写的越权字段，或是被调方法的第一个调用（如 IsCompleted 开头的类初始化）。
                    if (!anchored.Overlaps(callee.Fields) && (call is null || !FirstCalls(callee).Contains(call.Invocation.Method))) continue;
                    if (new Matcher(caller, blocks, block, i, callee, boolean, next).Match() is { } result)
                    {
                        next--;
                        return result;
                    }
                }
            }
        return null;
    }

    private static readonly Dictionary<ManagedBody, HashSet<MethodRef>> firstCalls = new(ReferenceEqualityComparer.Instance);

    /// <summary>被调方法入口附近的第一个调用（区域可以从它开始）。</summary>
    private static HashSet<MethodRef> FirstCalls(Callee callee)
    {
        lock (firstCalls)
        {
            if (!firstCalls.TryGetValue(callee.Body, out var set))
                firstCalls[callee.Body] = set = callee.Body.Blocks.Take(2).SelectMany(b => b.Statements).OfType<ManagedCall>().Take(1).Select(c => c.Invocation.Method).ToHashSet();
            return set;
        }
    }

    // ---------- 单字段包装（UniTask.Awaiter） ----------

    /// <summary>
    /// 单字段包装结构体的构造：<c>awaiter.task = t</c>（task 是 UniTask.Awaiter 唯一的只读私有字段，原生代码内联了构造函数）
    /// 改写成在 awaiter 上调用构造函数 <c>Awaiter(in UniTask task)</c>。构造函数须是该结构体只有一个参数（t 的类型或其 in/ref）的实例构造，
    /// 方法体（无分支、无其他调用）只把参数写入这个字段。在自己的构造函数里写只读字段是合法 IL（ECMA-335 II.16.1.2）。
    /// </summary>
    public static ManagedBody RewriteWrappers(ManagedBody body, IReadOnlyList<Callee> callees, Func<FieldRef, bool> blocked, Func<TypeRef, int> fields)
    {
        var changed = false;
        var blocks = body.Blocks.Select(block =>
        {
            var statements = new List<ManagedStatement>();
            foreach (var statement in block.Statements)
            {
                if (statement is ManagedStore { Target: IndirectValue { Address: AddressValue { Target: FieldValue { Receiver: { Type: ByRefRef } outer } field } }, Value: var value } store
                    && blocked(field.Field) && field.Field.DeclaringType is DefinitionRef wrapper && fields(wrapper) == 1
                    && (value is LocalValue || value is IndirectValue { Address.Type: ByRefRef })
                    && callees.FirstOrDefault(c => IsWrapperConstructor(c, field.Field, wrapper, value.Type)) is { } constructor)
                {
                    var parameter = constructor.Method.Method.Parameters[0].Type;
                    ManagedValue argument = parameter is ByRefRef ? value is LocalValue local ? new AddressValue(local) : ((IndirectValue)value).Address : value;
                    statements.Add(new ManagedCall(store.Address, new ManagedInvocation(constructor.Method, outer, [argument], false), null, false) { Inlined = true });
                    changed = true;
                    continue;
                }
                statements.Add(statement);
            }
            return block with { Statements = statements };
        }).ToArray();
        return changed ? body with { Blocks = blocks } : body;
    }

    private static bool IsWrapperConstructor(Callee callee, FieldRef field, TypeRef wrapper, TypeRef wrapped)
    {
        var definition = callee.Method.Method;
        if (definition.IsStatic || definition.Name != ".ctor" || definition.Parameters.Count != 1 || !callee.Method.DeclaringType.Equals(wrapper)) return false;
        var parameter = definition.Parameters[0].Type;
        if (!(parameter.Equals(wrapped) || parameter is ByRefRef r && r.Element.Equals(wrapped))) return false;
        var blocks = callee.Body.Blocks.ToDictionary(b => b.Address);
        var stored = false;
        var locals = new Dictionary<Variable, ManagedValue>();
        ManagedValue Resolve(ManagedValue v) => v is LocalValue l && locals.TryGetValue(l.Variable, out var known) ? known : v;
        var current = callee.Body.Blocks[0];
        for (var guard = 0; guard < 16; guard++)
        {
            foreach (var statement in current.Statements)
                switch (statement)
                {
                    case ManagedCall { Invocation.Method.Method.Name: "RunClassConstructor" }: break;
                    case ManagedAssignment a: locals[a.Target.Variable] = Resolve(a.Value); break;
                    case ManagedStore s when !stored && Target(s.Target) is FieldValue { Receiver: ArgumentValue { Index: -1 } } f && f.Field.Equals(field)
                        && Resolve(s.Value) is ArgumentValue { Index: 0 } or IndirectValue { Address: ArgumentValue { Index: 0 } }:
                        stored = true;
                        break;
                    case ManagedJump j when blocks.TryGetValue(j.Edge.Target, out var next) && j.Edge.Copies.Count == 0: current = next; goto continued;
                    case ManagedReturn { Value: null }: return stored;
                    default: return false;
                }
            return false;
            continued:;
        }
        return false;
    }

    private static ManagedValue Target(ManagedValue target) => target is IndirectValue { Address: AddressValue a } ? a.Target : target;

    /// <summary>字段链：根（参数）与从根出发的字段序列（剥去取址）。</summary>
    private static (ArgumentValue Root, List<FieldRef> Fields)? Chain(ManagedValue value)
    {
        var fields = new List<FieldRef>();
        while (true)
        {
            switch (value)
            {
                case FieldValue f: fields.Insert(0, f.Field); value = f.Receiver; continue;
                case AddressValue a: value = a.Target; continue;
                case ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } c when c.Width == c.Operand.Width: value = c.Operand; continue;
                case ArgumentValue root: return (root, fields);
                default: return null;
            }
        }
    }

    // ---------- 事件 ----------

    private abstract record Item;
    private sealed record CallItem(ManagedInvocation Invocation, LocalValue? Result) : Item;
    private sealed record StoreItem(ManagedValue Target, ManagedValue Value) : Item;
    private sealed record CheckItem(ManagedValue Condition, MethodRef Exception) : Item;
    private sealed record ReturnItem(ManagedValue? Value) : Item;
    private sealed record ExitItem(ulong Target, IReadOnlyList<ManagedCopy> Copies) : Item;
    private sealed record FailItem(string Reason) : Item;

    /// <summary>一组随机取值：叶子按结构取值（同一叶子在两侧相同）。</summary>
    private sealed class Valuation(int seed, IReadOnlyList<ulong> constants)
    {
        private readonly Dictionary<ManagedValue, ulong> leaves = new();
        private ulong state = 0x9E3779B97F4A7C15UL * (ulong)(seed + 1);

        private ulong Random()
        {
            state += 0x9E3779B97F4A7C15UL;
            var z = state;
            z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
            z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
            return z ^ (z >> 31);
        }

        public ulong Leaf(ManagedValue value)
        {
            if (leaves.TryGetValue(value, out var known)) return known;
            var r = Random();
            // 偏向 0（null、false、Pending）、小整数与两侧比较中出现的常量（及其 ±1），让各个分支都能走到。
            var v = (r % 10) switch
            {
                0 or 1 => 0UL, 2 => 1UL, 3 => 2UL, 4 => ulong.MaxValue,
                5 or 6 or 7 when constants.Count > 0 => constants[(int)(Random() % (ulong)constants.Count)],
                _ => Random(),
            };
            return leaves[value] = v & Mask(value.Width);
        }
    }

    private static ulong Mask(int width) => width is <= 0 or >= 64 ? ulong.MaxValue : (1UL << width) - 1;

    private static ulong SignExtend(ulong value, int width) => width is <= 0 or >= 64 ? value
        : (value & (1UL << (width - 1))) != 0 ? value | ~Mask(width) : value & Mask(width);

    private static ulong Eval(ManagedValue value, Valuation valuation)
    {
        switch (value)
        {
            case ConstantValue c: return c.Bits & Mask(c.Width);
            case ConversionValue { Kind: ConvKind.ZeroExtend } c: return Eval(c.Operand, valuation) & Mask(c.Operand.Width) & Mask(c.Width);
            case ConversionValue { Kind: ConvKind.SignExtend } c: return SignExtend(Eval(c.Operand, valuation), c.Operand.Width) & Mask(c.Width);
            case ConversionValue { Kind: ConvKind.Truncate or ConvKind.Bitcast } c: return Eval(c.Operand, valuation) & Mask(c.Width);
            case BinaryValue b when b.Op is BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr:
            {
                var l = Eval(b.Left, valuation);
                var r = Eval(b.Right, valuation);
                var shift = (int)(r & (ulong)(Math.Max(b.Width, 1) - 1));
                var result = b.Op switch
                {
                    BinOp.Add => l + r, BinOp.Sub => l - r, BinOp.Mul => l * r,
                    BinOp.And => l & r, BinOp.Or => l | r, BinOp.Xor => l ^ r,
                    BinOp.Shl => l << shift, BinOp.LShr => (l & Mask(b.Width)) >> shift,
                    _ => (ulong)((long)SignExtend(l, b.Width) >> shift),
                };
                return result & Mask(b.Width);
            }
            case UnaryValue { Op: UnOp.Neg } u: return (0 - Eval(u.Operand, valuation)) & Mask(u.Width);
            case UnaryValue { Op: UnOp.Not } u: return ~Eval(u.Operand, valuation) & Mask(u.Width);
            case ComparisonValue c when c.Condition <= Cond.Uge:
            {
                var width = Math.Max(c.Left.Width, c.Right.Width);
                var l = Eval(c.Left, valuation) & Mask(width);
                var r = Eval(c.Right, valuation) & Mask(width);
                long sl = (long)SignExtend(l, width), sr = (long)SignExtend(r, width);
                return c.Condition switch
                {
                    Cond.Eq => l == r, Cond.Ne => l != r,
                    Cond.Slt => sl < sr, Cond.Sle => sl <= sr, Cond.Sgt => sl > sr, Cond.Sge => sl >= sr,
                    Cond.Ult => l < r, Cond.Ule => l <= r, Cond.Ugt => l > r, _ => l >= r,
                } ? 1UL : 0UL;
            }
            case ChoiceValue c: return Eval(c.Condition, valuation) != 0 ? Eval(c.True, valuation) & Mask(c.Width) : Eval(c.False, valuation) & Mask(c.Width);
            case BooleanValue b:
            {
                var l = Eval(b.Left, valuation) != 0;
                var r = Eval(b.Right, valuation) != 0;
                return (b.IsAnd ? l && r : l || r) ? 1UL : 0UL;
            }
            case NegatedValue n: return Eval(n.Operand, valuation) == 0 ? 1UL : 0UL;
            default:
                // 字段、静态字段、数组、调用结果、区域外局部变量与参数，以及不解释的运算（浮点等）：按结构取值。
                return valuation.Leaf(value);
        }
    }

    private static bool Contains(ManagedValue value, Func<ManagedValue, bool> predicate) => ManagedValues.Walk(value).Any(predicate);

    private static ManagedValue Substitute(ManagedValue value, Func<ManagedValue, ManagedValue?> replace) =>
        replace(value) ?? ManagedValues.Map(value, child => Substitute(child, replace));

    /// <summary>本层的属性（不含子项）相同：子项换成同类型的占位值后比较。</summary>
    private static bool SameShape(ManagedValue a, ManagedValue b) =>
        a.GetType() == b.GetType() && ManagedValues.Map(a, c => new ConstantValue(0x5EED, c.Type, c.Width)).Equals(ManagedValues.Map(b, c => new ConstantValue(0x5EED, c.Type, c.Width)));

    // ---------- 匹配 ----------

    private sealed class Matcher(ManagedBody caller, Dictionary<ulong, ManagedBlock> blocks, ManagedBlock startBlock, int startIndex, Callee calleeMethod, TypeRef boolean, int variable)
    {
        private readonly Callee callee = calleeMethod;
        private TypeRef BooleanType => boolean;
        private readonly ManagedBlock start = startBlock;
        private readonly int index = startIndex;
        private readonly Dictionary<ulong, ManagedBlock> callerBlocks = blocks;
        private readonly Dictionary<ulong, ManagedBlock> calleeBlocks = calleeMethod.Pattern.Blocks.ToDictionary(b => b.Address);
        /// <summary>被调方法的参数（-1 为 this）→ 调用者中的值。</summary>
        private readonly Dictionary<int, ManagedValue> arguments = new();
        private readonly HashSet<ulong> region = [];
        private readonly HashSet<Variable> internals = [];
        private readonly List<(ulong Target, IReadOnlyList<ManagedCopy> Copies, ulong? Returned)> exits = [];
        /// <summary>返回值作为值使用（非 void、非 bool 的标量）：各出口上返回值与出口复制的取值，用于找出承载返回值的那个复制。</summary>
        private readonly List<(int Exit, ulong Value, ulong[] Copies)> returnedValues = [];
        private bool ValueResult => !callee.ReturnsBool && !ManagedTypes.IsVoid(callee.Method.Method.ReturnType);

        public ManagedBody? Match()
        {
            if (callee.Pattern.Regions.Count > 0 || !BindAnchors()) { Trace($"{callee.Method} @0x{start.Address:x}[{index}] 参数绑定失败"); return null; }
            var constants = Constants();
            for (var run = 0; run < Runs; run++)
                if (!Simulate(new Valuation(run, constants))) { Trace($"{callee.Method} @0x{start.Address:x}[{index}] 第 {run} 次同步执行失败：{failure}"); return null; }
            // 区域内调用者的每个分支两个方向都要实际走到过：没走到的路径可能是被调方法之外的代码（例如另一个状态的分派）。
            if (branches.Any(b => b.Value != 3)) { failure = "区域内有分支只走到一个方向"; Trace($"{callee.Method} @0x{start.Address:x}[{index}] {failure}"); return null; }
            var built = Build();
            Trace($"{callee.Method} @0x{start.Address:x}[{index}] {(built is null ? "改写条件不满足：" + failure : "认回")}");
            return built;
        }

        private string failure = "";
        /// <summary>调用者区域内的分支 → 走到过的方向（位 1：真，位 2：假；switch 按项计）。</summary>
        private readonly Dictionary<ManagedStatement, int> branches = new(ReferenceEqualityComparer.Instance);

        /// <summary>两侧比较中出现的常量及其 ±1（调用者取起点附近）。</summary>
        private List<ulong> Constants()
        {
            var values = callee.Pattern.Blocks.SelectMany(b => b.Statements)
                .Concat(callerBlocks.Values.Where(b => b == start || Targets(start.Statements[^1]).Contains(b.Address)).SelectMany(b => b.Statements))
                .Concat(callerBlocks.Values.SelectMany(b => b.Statements))
                .SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk).OfType<ComparisonValue>()
                .SelectMany(c => new[] { c.Left, c.Right }).OfType<ConstantValue>().Select(c => c.Bits).Distinct().Take(64).ToList();
            return values.SelectMany(v => new[] { v, v + 1, v - 1 }).Distinct().ToList();
        }

        /// <summary>
        /// 被调方法里以参数为根的字段链，与起点附近调用者的字段链按结构统一，得到参数的绑定。
        /// 按离起点的距离（块数）由近到远找：最近一层里候选唯一才绑定，多个 awaiter 时不会选到远处的另一个。
        /// </summary>
        private bool BindAnchors()
        {
            var calleeLeaves = callee.Pattern.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
                .Where(v => v is FieldValue f && Contains(f.Receiver, IsParameter)).Distinct().ToArray();
            if (calleeLeaves.Length == 0) return true;
            var layers = new List<List<ManagedValue>>();
            var seen = new HashSet<ulong>();
            var frontier = new List<(ManagedBlock Block, int From)> { (start, index) };
            for (var depth = 0; depth <= 6 && frontier.Count > 0; depth++)
            {
                var layer = new List<ManagedValue>();
                var next = new List<(ManagedBlock, int)>();
                foreach (var (block, from) in frontier)
                    foreach (var statement in block.Statements.Skip(from))
                    {
                        layer.AddRange(ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).Where(v => v is FieldValue));
                        foreach (var target in Targets(statement))
                            if (callerBlocks.TryGetValue(target, out var successor) && seen.Add(target)) next.Add((successor, 0));
                    }
                layers.Add(layer.Distinct().ToList());
                frontier = next;
            }
            foreach (var leaf in calleeLeaves)
                foreach (var layer in layers)
                {
                    var bindings = layer.Select(v =>
                    {
                        var trial = new Dictionary<int, ManagedValue>(arguments);
                        return Unify(leaf, v, trial) ? trial : null;
                    }).OfType<Dictionary<int, ManagedValue>>().DistinctBy(t => string.Join("|", t.OrderBy(p => p.Key).Select(p => $"{p.Key}={p.Value}"))).ToArray();
                    if (bindings.Length > 1) return false;
                    if (bindings.Length == 0) continue;
                    foreach (var (k, v) in bindings[0]) arguments[k] = v;
                    break;
                }
            return arguments.Count > 0;
        }

        private static IEnumerable<ulong> Targets(ManagedStatement statement) => ManagedValues.Edges(statement).Select(e => e.Target);

        /// <summary>被调方法的值（含参数）与调用者的值按结构统一；参数第一次出现时绑定。</summary>
        private static bool Unify(ManagedValue pattern, ManagedValue value, Dictionary<int, ManagedValue> binding)
        {
            if (pattern is ArgumentValue argument && IsParameter(argument))
            {
                var key = argument.Index + Shift;
                if (binding.TryGetValue(key, out var bound)) return bound.Equals(value);
                if (!argument.Type.Equals(value.Type)) return false;
                binding[key] = value;
                return true;
            }
            if (!SameShape(pattern, value)) return false;
            var p = ManagedValues.Children(pattern).ToArray();
            var v = ManagedValues.Children(value).ToArray();
            if (p.Length != v.Length) return false;
            for (var i = 0; i < p.Length; i++)
                if (!Unify(p[i], v[i], binding)) return false;
            return true;
        }

        /// <summary>两侧在同一组取值下同步执行一遍。</summary>
        private bool Simulate(Valuation valuation)
        {
            var results = new Dictionary<Variable, LocalValue>();
            var inner = new Cursor(this, valuation, results, isCallee: true);
            var outer = new Cursor(this, valuation, results, isCallee: false);
            for (var step = 0; step < 64; step++)
            {
                var expected = inner.Next(false);
                var actual = outer.Next(expected is ReturnItem);
                failure = $"期望 {Describe(expected)}，实际 {Describe(actual)}";
                switch (expected, actual)
                {
                    case (FailItem, _) or (_, FailItem): return false;
                    case (ReturnItem r, ExitItem e):
                        ulong? returned = callee.ReturnsBool && r.Value is { } v ? (Eval(inner.Resolve(v), valuation) != 0 ? 1UL : 0UL) : null;
                        if (ValueResult)
                        {
                            // 只认标量的返回值；结构体返回值逐叶子进入调用者，这里不对应。
                            if (r.Value is not { Width: > 0 and <= 64 } value) return false;
                            returnedValues.Add((exits.Count, Eval(inner.Resolve(value), valuation),
                                e.Copies.Select(c => c.Value.Width is > 0 and <= 64 ? Eval(outer.Resolve(c.Value), valuation) : ulong.MaxValue).ToArray()));
                        }
                        exits.Add((e.Target, e.Copies, returned));
                        return true;
                    case (CallItem c, CallItem d):
                        if (!c.Invocation.Method.Equals(d.Invocation.Method) || (c.Invocation.Receiver is null) != (d.Invocation.Receiver is null)
                            || c.Invocation.Arguments.Count != d.Invocation.Arguments.Count) return false;
                        if (c.Invocation.Receiver is { } cr && !Same(inner, outer, cr, d.Invocation.Receiver!, valuation)) { failure += "（接收者不同）"; return false; }
                        for (var k = 0; k < c.Invocation.Arguments.Count; k++)
                            if (!Same(inner, outer, c.Invocation.Arguments[k], d.Invocation.Arguments[k], valuation)) { failure += $"（实参 {k} 不同）"; return false; }
                        // 调用者丢弃了结果（如 await 不取值时内联的 GetResult）：被调方的结果绑定为一个不透明的叶子，出口不能依赖它。
                        if (c.Result is null && d.Result is not null) { failure += "（结果有无不同）"; return false; }
                        if (c.Result is { } cv) results[cv.Variable] = d.Result ?? new LocalValue(new Variable(Storage.Temp(-1000 - cv.Variable.Version), 1), cv.Type, cv.Width);
                        break;
                    case (StoreItem c, StoreItem d):
                        if (!Same(inner, outer, c.Target, d.Target, valuation, structural: true) || !Same(inner, outer, c.Value, d.Value, valuation)) return false;
                        break;
                    case (CheckItem c, CheckItem d):
                        if (!c.Exception.Equals(d.Exception) || Eval(inner.Resolve(c.Condition), valuation) != Eval(outer.Resolve(d.Condition), valuation)) return false;
                        // 检查成立时两侧都抛出同一种异常，路径到此为止。
                        if (Eval(outer.Resolve(d.Condition), valuation) != 0) return true;
                        break;
                    default: return false;
                }
            }
            return false;
        }

        private static string Describe(Item item) => item switch
        {
            CallItem c => $"调用 {c.Invocation.Method}",
            StoreItem s => $"写入 {s.Target.GetType().Name}",
            CheckItem => "检查",
            ReturnItem => "返回",
            ExitItem e => $"出口 0x{e.Target:x}",
            FailItem f => $"失败（{f.Reason}）",
            _ => item.GetType().Name,
        };

        /// <summary>同一个值：参数先按结构绑定；标量比较随机取值下的结果，地址与结构体值比较结构。</summary>
        private bool Same(Cursor inner, Cursor outer, ManagedValue pattern, ManagedValue value, Valuation valuation, bool structural = false)
        {
            var resolved = outer.Resolve(value);
            var raw = inner.Resolve(pattern, bind: false);
            if (Contains(raw, IsParameter))
            {
                if (!Unify(raw, resolved, arguments)) return false;
                raw = inner.Resolve(pattern);
            }
            if (structural || value.Width == 0 || value.Type is ByRefRef) return raw.Equals(resolved);
            if (raw.Width != resolved.Width && !(raw.Width <= 8 && resolved.Width <= 8)) return false;
            return Eval(raw, valuation) == Eval(resolved, valuation);
        }

        /// <summary>沿一侧的控制流执行到下一个事件（调用、写入、检查）或终点（被调方法返回、调用者离开区域）。</summary>
        private sealed class Cursor(Matcher owner, Valuation valuation, Dictionary<Variable, LocalValue> results, bool isCallee)
        {
            private readonly Dictionary<Variable, ManagedValue> environment = new();
            private readonly HashSet<ulong> visited = [];
            private ManagedBlock block = isCallee ? owner.callee.Pattern.Blocks[0] : owner.start;
            private int position = isCallee ? 0 : owner.index;
            private int steps;

            /// <summary>代入区域内（被调方法内）已求值的局部变量；被调方法的参数与调用结果换成调用者的值。</summary>
            public ManagedValue Resolve(ManagedValue value, bool bind = true) => Substitute(value, v => v switch
            {
                LocalValue l when environment.TryGetValue(l.Variable, out var known) => known,
                LocalValue l when isCallee && results.TryGetValue(l.Variable, out var mapped) => mapped,
                ArgumentValue a when isCallee && bind && IsParameter(a) && owner.arguments.TryGetValue(a.Index + Shift, out var bound) => bound,
                _ => null,
            });

            private bool Internal(ManagedValue value) => !isCallee && Contains(value, v => v is LocalValue l && owner.internals.Contains(l.Variable));

            public Item Next(bool calleeReturned)
            {
                while (true)
                {
                    // 尾调用之后被调方法以调用结果返回。
                    if (tail) return new ReturnItem(tailResult);
                    if (++steps > StepLimit) return new FailItem("步数");
                    if (position == 0 && !visited.Add(block.Address)) return new FailItem("回边");
                    if (!isCallee) owner.region.Add(block.Address);
                    if (position >= block.Statements.Count) return new FailItem("块没有终结语句");
                    var statement = block.Statements[position++];
                    switch (statement)
                    {
                        case ManagedAssignment a:
                            environment[a.Target.Variable] = Resolve(a.Value);
                            if (!isCallee) owner.internals.Add(a.Target.Variable);
                            continue;
                        case ManagedCall c when !c.Tail || isCallee:
                        {
                            var invocation = c.Invocation;
                            if (!isCallee && c.Result is { } local) owner.internals.Add(local.Variable);
                            // 被调方以尾调用的结果返回：合成结果变量，与调用者的调用结果绑定。
                            var result = c.Result ?? (c.Tail && owner.callee.ReturnsBool ? new LocalValue(new Variable(Storage.Temp(-2000 - position), 1), owner.BooleanType, 8) : null);
                            var item = new CallItem(invocation, result);
                            if (c.Tail) { tail = true; tailResult = result; }
                            return item;
                        }
                        case ManagedStore s: return new StoreItem(s.Target, s.Value);
                        case ManagedCheck check: return new CheckItem(check.Condition, check.Exception);
                        case ManagedReturn r when isCallee: return new ReturnItem(r.Value);
                        case ManagedJump j:
                        {
                            if (Move(j.Edge, calleeReturned) is { } exit) return exit;
                            continue;
                        }
                        case ManagedBranch b:
                        {
                            var taken = Eval(Resolve(b.Condition), valuation) != 0;
                            if (!isCallee) owner.branches[b] = owner.branches.GetValueOrDefault(b) | (taken ? 1 : 2);
                            if (Move(taken ? b.Taken : b.Fallthrough, calleeReturned) is { } exit) return exit;
                            continue;
                        }
                        case ManagedSwitch w:
                        {
                            var selector = Eval(Resolve(w.Index), valuation) & 0xffffffff;
                            // switch 只要求不止一个方向；完整覆盖由各项目标的分支检查补足。
                            if (!isCallee) owner.branches[w] = owner.branches.GetValueOrDefault(w) | (selector == 0 ? 1 : 2);
                            if (Move(w.Cases[selector < (ulong)w.Cases.Count ? (int)selector : 0], calleeReturned) is { } exit) return exit;
                            continue;
                        }
                        default:
                            return new FailItem($"语句 {statement.GetType().Name}");
                    }
                }
            }

            private bool tail;
            private LocalValue? tailResult;

            private ExitItem? Move(ManagedEdge edge, bool calleeReturned)
            {
                if (!isCallee && calleeReturned && !owner.region.Contains(edge.Target) && !References(edge.Target))
                    return new ExitItem(edge.Target, edge.Copies);
                // 边上的复制同时生效：先求全部源值。
                var values = edge.Copies.Select(c => Resolve(c.Value)).ToArray();
                for (var k = 0; k < values.Length; k++)
                {
                    environment[edge.Copies[k].Target.Variable] = values[k];
                    if (!isCallee) owner.internals.Add(edge.Copies[k].Target.Variable);
                }
                var map = isCallee ? owner.calleeBlocks : owner.callerBlocks;
                if (!map.TryGetValue(edge.Target, out var next)) return new ExitItem(edge.Target, edge.Copies);
                block = next;
                position = 0;
                return null;
            }

            private bool References(ulong target) => owner.callerBlocks.TryGetValue(target, out var next)
                && next.Statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).Any(Internal);
        }

        // ---------- 改写 ----------

        private ManagedBody? Build()
        {
            var definition = callee.Method.Method;
            if (!definition.IsStatic && !arguments.ContainsKey(-1) || Enumerable.Range(0, definition.Parameters.Count).Any(k => !arguments.ContainsKey(k))) { failure = "参数未全部绑定"; return null; }
            if (exits.Count == 0) { failure = "没有出口"; return null; }
            var predecessors = caller.Blocks.SelectMany(b => b.Statements.SelectMany(Targets).Select(t => (From: b.Address, To: t))).ToLookup(e => e.To, e => e.From);
            // 出口处只有一条无复制跳转的空块，前驱都在区域内时并入区域，出口改为它的目标（各路径经不同的空块到达同一处）。
            bool Empty(ulong a) => callerBlocks.TryGetValue(a, out var b) && b.Statements is [ManagedJump { Edge.Copies.Count: 0 }];
            for (var changed = true; changed;)
            {
                changed = false;
                for (var k = 0; k < exits.Count; k++)
                {
                    var exit = exits[k];
                    if (exit.Copies.Count == 0 && Empty(exit.Target) && exit.Target != start.Address && predecessors[exit.Target].All(region.Contains))
                    {
                        region.Add(exit.Target);
                        exits[k] = (((ManagedJump)callerBlocks[exit.Target].Statements[0]).Edge.Target, [], exit.Returned);
                        changed = true;
                    }
                }
            }
            // 区域单入口：除起点外，每个区域块的前驱都在区域内；起点块不在区域内被再次进入。
            foreach (var address in region)
                if (address != start.Address && predecessors[address].Any(p => !region.Contains(p))) { failure = $"区域块 0x{address:x} 有区域外前驱"; return null; }
            if (predecessors[start.Address].Any(region.Contains)) { failure = "区域回到起点"; return null; }
            // 异常区域：区域内各块所属的 try/handler 与起点相同，且都不是 handler 入口。
            string Membership(ulong address) => string.Join(",", caller.Regions.Select((r, k) => (r.Try.Contains(address) ? "t" : "") + (r.Handler.Contains(address) ? "h" : "") + k));
            var membership = Membership(start.Address);
            if (region.Any(a => Membership(a) != membership || a != start.Address && caller.Regions.Any(r => r.HandlerEntry == a))) { failure = "区域跨越异常区域"; return null; }
            // 区域内定义的局部变量在区域外不再使用。
            var outside = caller.Blocks.Where(b => !region.Contains(b.Address)).SelectMany(b => b.Statements)
                .Concat(start.Statements.Take(index))
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.Edges(s).SelectMany(e => e.Copies).SelectMany(c => new ManagedValue[] { c.Target, c.Value })));
            if (outside.Any(v => Contains(v, x => x is LocalValue l && internals.Contains(l.Variable)))) { failure = "区域内的局部变量在区域外使用"; return null; }
            // 承载返回值的出口复制：每个出口上都有一个写同一局部变量的复制，在每组取值下都等于返回值；调用的结果就是这个局部变量。
            LocalValue? resultLocal = null;
            if (ValueResult)
            {
                var candidates = exits[0].Copies.Select(c => c.Target).Where(target => returnedValues.All(v =>
                {
                    var index = exits[v.Exit].Copies.Select((c, k) => (c, k)).Where(p => p.c.Target.Variable == target.Variable).Select(p => p.k).DefaultIfEmpty(-1).First();
                    return index >= 0 && v.Copies[index] == v.Value;
                })).ToArray();
                // 没有这样的复制：返回值不进入调用者（区域内的值不在区域外使用由下面检查），结果丢弃。
                if (candidates.Length > 1) { failure = $"返回值没有唯一的出口复制：{candidates.Length}"; return null; }
                var returnType = definition.ReturnType.Substitute(callee.Method.TypeArguments, callee.Method.MethodArguments);
                if (candidates is [var only])
                {
                    if (!only.Type.Equals(returnType)) { failure = $"承载返回值的局部变量类型 {only.Type} 与返回类型 {returnType} 不同"; return null; }
                    resultLocal = only;
                    for (var k = 0; k < exits.Count; k++)
                        exits[k] = (exits[k].Target, exits[k].Copies.Where(c => c.Target.Variable != only.Variable).ToArray(), exits[k].Returned);
                }
            }
            if (exits.Any(e => e.Copies.Any(c => Contains(c.Value, x => x is LocalValue l && internals.Contains(l.Variable)) || internals.Contains(c.Target.Variable)))) { failure = "出口复制使用区域内的值"; return null; }

            var invocation = new ManagedInvocation(callee.Method, definition.IsStatic ? null : arguments[-1],
                Enumerable.Range(0, definition.Parameters.Count).Select(k => arguments[k]).ToArray(),
                !definition.IsStatic && arguments[-1].Type is not ByRefRef && definition.IsVirtual);
            var statements = start.Statements.Take(index).ToList();
            var site = start.Statements[index].Address;
            var targets = exits.Select(e => (e.Target, Copies: string.Join(";", e.Copies))).Distinct().ToArray();
            if (callee.ReturnsBool)
            {
                var whenTrue = exits.Where(e => e.Returned == 1).Select(e => (e.Target, e.Copies)).DistinctBy(e => (e.Target, string.Join(";", e.Copies))).ToArray();
                var whenFalse = exits.Where(e => e.Returned == 0).Select(e => (e.Target, e.Copies)).DistinctBy(e => (e.Target, string.Join(";", e.Copies))).ToArray();
                if (whenTrue.Length == 1 && whenFalse.Length == 1 && whenTrue[0].Target != whenFalse[0].Target)
                {
                    var result = new LocalValue(new Variable(Storage.Temp(variable), 1), boolean, 8);
                    statements.Add(new ManagedCall(site, invocation, result, false) { Inlined = true });
                    statements.Add(new ManagedBranch(site, new ComparisonValue(Cond.Ne, result, new ConstantValue(0, boolean, 8), boolean),
                        new ManagedEdge(whenTrue[0].Target, whenTrue[0].Copies), new ManagedEdge(whenFalse[0].Target, whenFalse[0].Copies)));
                }
                else if (targets.Length == 1)
                {
                    statements.Add(new ManagedCall(site, invocation, null, false) { Inlined = true });
                    statements.Add(new ManagedJump(site, new ManagedEdge(exits[0].Target, exits[0].Copies)));
                }
                else { failure = $"bool 出口不唯一：真 {whenTrue.Length}，假 {whenFalse.Length}"; return null; }
            }
            else
            {
                if (targets.Length != 1) { failure = $"出口不唯一：{targets.Length}"; return null; }
                statements.Add(new ManagedCall(site, invocation, resultLocal, false) { Inlined = true });
                statements.Add(new ManagedJump(site, new ManagedEdge(exits[0].Target, exits[0].Copies)));
            }
            var removed = region.Where(a => a != start.Address).ToHashSet();
            return caller with
            {
                Blocks = caller.Blocks.Where(b => !removed.Contains(b.Address)).Select(b => b == start ? b with { Statements = statements } : b).ToArray(),
                Regions = caller.Regions.Select(r => r with { Try = r.Try.Where(a => !removed.Contains(a)).ToArray(), Handler = r.Handler.Where(a => !removed.Contains(a)).ToArray() }).ToArray(),
            };
        }
    }
}
