using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Output;

/// <summary>
/// 沿可达控制流验证 this 初始化；元数据准备、独立参数计算和本类字段初始化可以先于基类调用。
/// 基类调用之前对本类字段的写入在 C# 里只能是字段初始化器（C# 先执行字段初始化器，再求基类构造的实参），所以还要求：
/// 写入位于入口块、排在实参计算之前、不引用参数，构造函数不以 this(...) 链接。
/// ILSpy 只在本类各个不以 this(...) 链接的构造函数的前导写入都相同时才还原字段初始化器，这一条由调用方在类型层面用 <see cref="Shape"/> 检查。
/// </summary>
internal static class ConstructorInitialization
{
    /// <summary>ChainsWithThis：调用本类构造函数；Initializers：字段初始化器的规范形式（字段与值），按写入顺序。</summary>
    public sealed record Shape(bool ChainsWithThis, IReadOnlyList<string> Initializers);

    public static string? Check(ManagedBody body, out Shape shape)
    {
        shape = new Shape(false, []);
        var owner = body.Method.Method.Owner;
        var definitions = new Dictionary<Variable, List<ManagedValue>>();
        var uses = new Dictionary<Variable, int>();
        void Define(LocalValue local, ManagedValue value)
        {
            if (!definitions.TryGetValue(local.Variable, out var values)) definitions.Add(local.Variable, values = []);
            values.Add(value);
        }
        void Use(ManagedValue value)
        {
            foreach (var local in ManagedValues.Walk(value).OfType<LocalValue>()) uses[local.Variable] = uses.GetValueOrDefault(local.Variable) + 1;
        }
        IEnumerable<ManagedEdge> Edges(ManagedStatement statement) => ManagedValues.Edges(statement);
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment assignment) Define(assignment.Target, assignment.Value);
            foreach (var value in ManagedValues.Of(statement).Where(v => statement is not ManagedAssignment a || !ReferenceEquals(v, a.Target))) Use(value);
            foreach (var copy in Edges(statement).SelectMany(e => e.Copies)) { Define(copy.Target, copy.Value); Use(copy.Value); }
        }
        bool IsThis(ManagedValue value)
        {
            var pending = new Stack<ManagedValue>(); pending.Push(value);
            var seen = new HashSet<Variable>();
            var found = false;
            while (pending.TryPop(out var current))
            {
                if (current is ArgumentValue { Index: -1 }) { found = true; continue; }
                if (current is not LocalValue local || !definitions.TryGetValue(local.Variable, out var sources)) return false;
                if (seen.Add(local.Variable)) foreach (var source in sources) pending.Push(source);
            }
            return found;
        }
        // 值（沿局部变量的定义展开）是否引用了满足 argument 的参数
        bool UsesArgument(ManagedValue value, Func<ArgumentValue, bool> argument)
        {
            var pending = new Stack<ManagedValue>(); pending.Push(value);
            var seen = new HashSet<Variable>();
            while (pending.TryPop(out var current))
            {
                if (current is ArgumentValue a && argument(a)) return true;
                if (current is LocalValue local && seen.Add(local.Variable) && definitions.TryGetValue(local.Variable, out var sources))
                    foreach (var source in sources) pending.Push(source);
                foreach (var child in ManagedValues.Children(current)) pending.Push(child);
            }
            return false;
        }
        bool UsesThis(ManagedValue value) => UsesArgument(value, a => a.Index == -1);
        bool IsInitialization(ManagedStatement statement) =>
            statement is ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: { } receiver } } && IsThis(receiver);
        FieldValue? OwnField(ManagedValue value) => value switch
        {
            IndirectValue { Address: AddressValue address } => OwnField(address.Target),
            FieldValue f when IsThis(f.Receiver) && f.Field.Field.Owner == owner => f,
            FieldValue { Receiver: AddressValue address } => OwnField(address.Target),
            _ => null,
        };
        bool IsOwnFieldStore(ManagedStatement statement) => statement is ManagedStore s && OwnField(s.Target) is not null;
        string StorePath(ManagedValue value) => value switch
        {
            IndirectValue { Address: AddressValue address } => StorePath(address.Target),
            FieldValue { Receiver: AddressValue address } field => StorePath(address.Target) + $".{field.Field.Field.Index}",
            FieldValue field => $"field#{field.Field.Field.Index}",
            _ => "",
        };

        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var queue = new Queue<(ulong Address, bool Initialized)>();
        queue.Enqueue((body.Blocks[0].Address, false));
        var visited = new HashSet<(ulong, bool)>();
        var targets = new HashSet<MethodRef>();
        var initializerStores = false;
        var beforeBase = new List<ManagedStatement>();
        while (queue.TryDequeue(out var state))
        {
            if (!visited.Add(state)) continue;
            var initialized = state.Initialized;
            foreach (var statement in blocks[state.Address].Statements)
            {
                if (statement is ManagedCall call && IsInitialization(call))
                {
                    var target = call.Invocation.Method;
                    if (initialized) return "构造函数路径重复初始化 this";
                    if (target.Method.IsStatic || target.Method.Owner != owner && target.DeclaringType != owner.BaseType)
                        return "构造函数没有调用本类或直接基类构造函数";
                    if (call.Invocation.Arguments.Any(UsesThis)) return "基类构造参数使用了未初始化的 this";
                    if (targets.Count > 0 && !targets.Contains(target)) return "构造函数 各路径调用的构造函数不同";
                    targets.Add(target);
                    initialized = true;
                }
                else if (!initialized)
                {
                    beforeBase.Add(statement);
                    initializerStores |= IsOwnFieldStore(statement);
                    var permitted = statement switch
                    {
                        ManagedAssignment a => IsThis(a.Value) || !UsesThis(a.Value),
                        ManagedStore s when IsOwnFieldStore(s) => !UsesThis(s.Value),
                        ManagedStore s => !UsesThis(s.Target) && !UsesThis(s.Value),
                        ManagedCall c => (c.Invocation.Receiver is null || !UsesThis(c.Invocation.Receiver)) && !c.Invocation.Arguments.Any(UsesThis),
                        ManagedJump => true,
                        ManagedBranch b => !UsesThis(b.Condition),
                        ManagedSwitch w => !UsesThis(w.Index),
                        ManagedCheck k => !UsesThis(k.Condition),
                        ManagedReturn => false,
                        _ => false,
                    };
                    if (!permitted) return "构造函数在基类初始化前读取或泄漏 this，或直接返回";
                }
                foreach (var edge in Edges(statement))
                {
                    if (!initialized && edge.Copies.Any(c => !IsThis(c.Value) && UsesThis(c.Value))) return "构造函数的边赋值使用了未初始化的 this";
                    queue.Enqueue((edge.Target, initialized));
                }
                if (statement is ManagedReturn or ManagedCall { Tail: true })
                    if (!initialized) return "构造函数的返回路径没有初始化 this";
            }
        }
        var chainsWithThis = targets.Any(t => t.Method.Owner == owner);
        if (!initializerStores)
        {
            shape = new Shape(chainsWithThis, []);
            return null;
        }

        // 字段初始化器：基类调用之前的本类字段写入，连同只为它们求值、只用一次的临时变量
        if (chainsWithThis) return "构造函数 以 this(...) 链接却先写本类字段，C# 无法表达";
        if (StraightPrefix(body, blocks, IsInitialization) is not { } prefix)
        {
            // 唯一构造函数的集合初始化可以带容量分支；仍在原位置写出，不能提前调用基类。
            if (owner.Methods.Count(m => m.Name == ".ctor" && !m.IsStatic) != 1
                || beforeBase.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .Any(v => UsesArgument(v, a => a.Index >= 0)))
                return "构造函数 字段初始化不在入口的直线路径上";
            shape = new Shape(false, [$"initializer-cfg#{body.Method.Method.Index}"]);
            return null;
        }
        Dictionary<Variable, int>? prefixLocals = null;
        string? Key(ManagedValue value)
        {
            string? Children(string head, IEnumerable<ManagedValue> children)
            {
                var keys = children.Select(Key).ToArray();
                return keys.Any(k => k is null) ? null : $"{head}({string.Join(", ", keys)})";
            }
            return value switch
            {
                LocalValue l when prefixLocals is not null => prefixLocals.TryGetValue(l.Variable, out var ordinal) ? $"v{ordinal}:{l.Type}" : null,
                LocalValue l => definitions.TryGetValue(l.Variable, out var d) && d.Count == 1 && uses.GetValueOrDefault(l.Variable) == 1 ? Key(d[0]) : null,
                ArgumentValue => null,
                ConstantValue c => $"{c.Type}:{c.Bits:x}/{c.Width}",
                StringValue s => $"\"{s.Text.Replace("\\", "\\\\").Replace("\"", "\\\"")}\"",
                TypeHandleValue t => $"typeof({t.Target})",
                StaticFieldValue f => $"{f.Field}",
                NewObjectValue n => Children($"new#{n.Constructor.Method.Index} {n.Constructor}", n.Arguments),
                NewArrayValue a => Children($"new {a.ArrayType}", [a.Length]),
                ComposedValue c => Children($"struct {c.StructType}:{string.Join("/", c.Leaves.Select(l => string.Join(".", l.Path.Select(f => f.Field.Index))))}", c.Leaves.Select(l => l.Value)),
                BoxValue b => Children($"box {b.Boxed} {b.ObjectType}", [b.Operand]),
                IsInstValue i => Children($"isinst {i.Target}", [i.Operand]),
                FieldValue f => Children($"{f.Field}", [f.Receiver]),
                AddressValue a => Children("address", [a.Target]),
                IndirectValue i => Children("indirect", [i.Address]),
                ArrayLengthValue a => Children($"len {a.Type}/{a.Width}", [a.Array]),
                ArrayElementValue a => Children($"elem {a.Type}/{a.Width}", [a.Array, a.Index]),
                BinaryValue b => Children($"{b.Op} {b.Type}/{b.Width}", [b.Left, b.Right]),
                UnaryValue u => Children($"{u.Op} {u.Type}/{u.Width}", [u.Operand]),
                ConversionValue c => Children($"{c.Kind} {c.Type}/{c.Width}", [c.Operand]),
                ComparisonValue c => Children($"{c.Condition} {c.Type}", [c.Left, c.Right]),
                ChoiceValue c => Children($"? {c.Type}/{c.Width}", [c.Condition, c.True, c.False]),
                BooleanValue b => Children($"{(b.IsAnd ? "&&" : "||")} {b.Type}", [b.Left, b.Right]),
                NegatedValue n => Children($"! {n.Type}", [n.Operand]),
                _ => null,
            };
        }
        // 数组和集合初始化会多次引用同一新对象，静态工厂也可参与求值。
        // 按原顺序比较完整前缀，局部变量按定义次序编号；不能只比较最后存入字段的 new 表达式。
        Shape? PrefixShape()
        {
            prefixLocals = new();
            var keys = new List<string>();
            var last = prefix.FindLastIndex(s => IsOwnFieldStore(s));
            string? Values(string head, IEnumerable<ManagedValue> values)
            {
                var items = values.Select(Key).ToArray();
                return items.Any(k => k is null) ? null : $"{head}({string.Join(", ", items)})";
            }
            for (var i = 0; i <= last; i++)
            {
                var statement = prefix[i];
                var key = statement switch
                {
                    ManagedAssignment a => Values("assign", [a.Value]),
                    ManagedStore s when IsOwnFieldStore(s) => Values(StorePath(s.Target), [s.Value]),
                    ManagedStore s => Values("store", [s.Target, s.Value]),
                    ManagedCall c when !c.Tail => Values($"call#{c.Invocation.Method.Method.Index}:{c.Invocation.Method}:{c.Invocation.Virtual}",
                        c.Invocation.Receiver is { } receiver ? [receiver, .. c.Invocation.Arguments] : c.Invocation.Arguments),
                    ManagedCheck c => Values($"check#{c.Exception.Method.Index}", [c.Condition]),
                    _ => null,
                };
                if (key is null) return null;
                var defined = statement switch { ManagedAssignment a => a.Target, ManagedCall c => c.Result, _ => null };
                if (defined is not null)
                {
                    if (!prefixLocals.TryAdd(defined.Variable, prefixLocals.Count)) return null;
                    key += $" -> v{prefixLocals[defined.Variable]}:{defined.Type}";
                }
                keys.Add(key);
            }
            return new Shape(false, keys);
        }
        var initializerLocals = new HashSet<Variable>();
        var initializers = new List<string>();
        foreach (var store in prefix.Where(IsOwnFieldStore).Cast<ManagedStore>())
        {
            if (UsesArgument(store.Value, a => a.Index >= 0)) return "构造函数 字段初始化器引用了参数";
            if (Key(store.Value) is not { } key)
            {
                if (PrefixShape() is not { } prefixShape) return "构造函数 字段初始化器的值尚未支持比较";
                shape = prefixShape;
                return null;
            }
            initializers.Add($"{StorePath(store.Target)} = {key}");
            foreach (var local in ManagedValues.Walk(store.Value).OfType<LocalValue>()) initializerLocals.Add(local.Variable);
            // Key 只展开只定义一次、只用一次的变量，因此一层层加入即可覆盖全部
            for (var added = true; added;)
            {
                added = false;
                foreach (var a in prefix.OfType<ManagedAssignment>().Where(a => initializerLocals.Contains(a.Target.Variable)))
                    foreach (var local in ManagedValues.Walk(a.Value).OfType<LocalValue>()) added |= initializerLocals.Add(local.Variable);
            }
        }
        var other = false;
        foreach (var statement in prefix)
        {
            var part = IsOwnFieldStore(statement) || statement is ManagedAssignment a && initializerLocals.Contains(a.Target.Variable);
            if (part && other) return "构造函数 字段初始化器与基类构造实参的计算交错";
            other |= !part;
        }
        shape = new Shape(false, initializers);
        return null;
    }

    /// <summary>从入口沿无条件跳转（去掉元数据守卫后入口块常只剩一个跳转）走到初始化调用之前的语句；中途有分支、边赋值或回到走过的块时为 null。</summary>
    private static List<ManagedStatement>? StraightPrefix(ManagedBody body, Dictionary<ulong, ManagedBlock> blocks, Func<ManagedStatement, bool> isInitialization)
    {
        var prefix = new List<ManagedStatement>();
        var visited = new HashSet<ulong>();
        for (var block = body.Blocks[0]; visited.Add(block.Address);)
        {
            ManagedBlock? next = null;
            foreach (var statement in block.Statements)
            {
                if (isInitialization(statement)) return prefix;
                if (statement is ManagedJump { Edge.Copies.Count: 0 } jump) next = blocks[jump.Edge.Target];
                else if (statement is ManagedJump or ManagedBranch or ManagedSwitch) return null;
                else prefix.Add(statement);
            }
            if (next is null) return null;
            block = next;
        }
        return null;
    }

    /// <summary>
    /// 类型层面的检查：某个构造函数有字段初始化器时，本类所有不以 this(...) 链接的实例构造函数都必须写出，且初始化器相同；
    /// 未写出的构造函数是骨架桩，无从知道它是否以 this(...) 链接，按不一致处理。返回不能写出的构造函数。
    /// </summary>
    public static IEnumerable<ManagedBody> Inconsistent(IEnumerable<(ManagedBody Body, Shape Shape)> constructors)
    {
        foreach (var group in constructors.GroupBy(c => c.Body.Method.Method.Owner))
        {
            var initializing = group.Where(c => c.Shape.Initializers.Count > 0).ToArray();
            if (initializing.Length == 0) continue;
            var shapes = group.ToDictionary(c => c.Body.Method.Method, c => c.Shape);
            var expected = initializing[0].Shape.Initializers;
            var consistent = group.Key.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic).All(m =>
                shapes.TryGetValue(m, out var shape) && (shape.ChainsWithThis || shape.Initializers.SequenceEqual(expected)));
            if (!consistent)
                foreach (var c in initializing) yield return c.Body;
        }
    }
}
