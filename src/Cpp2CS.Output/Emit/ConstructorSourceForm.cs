using Cpp2CS.Ir;

namespace Cpp2CS.Output;

/// <summary>验证已合法初始化的构造体能否表达为 C# 构造链和一致的字段初始化器。</summary>
internal static class ConstructorSourceForm
{
    public sealed record Shape(bool ChainsWithThis, IReadOnlyList<string> Initializers);

    public static string? Check(ManagedBody body, ConstructorInitialization.Analysis flow, out Shape shape)
    {
        shape = new(false, []);
        var owner = body.Method.Method.Owner;
        var values = flow.Values;
        var definitions = values.Definitions;
        var uses = values.Uses;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        if (flow.Targets.Count > 1) return "构造函数 各路径调用的构造函数不同，C# 无法表达";
        var chainsWithThis = flow.Targets.Any(t => t.Method.Owner == owner);
        if (!flow.InitializerStores)
        {
            shape = new Shape(chainsWithThis, []);
            return null;
        }

        // 字段初始化器：基类调用之前的本类字段写入，连同只为它们求值、只用一次的临时变量
        if (chainsWithThis) return "构造函数 以 this(...) 链接却先写本类字段，C# 无法表达";
        if (StraightPrefix(body, blocks, values.IsInitialization) is not { } prefix)
        {
            // 唯一构造函数的集合初始化可以带容量分支；仍在原位置写出，不能提前调用基类。
            if (owner.Methods.Count(m => m.Name == ".ctor" && !m.IsStatic) != 1
                || flow.BeforeBase.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                    .Any(v => values.UsesArgument(v, a => a.Index >= 0)))
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
                FieldHandleValue f => $"ldtoken({f.Field})",
                StaticFieldValue f => $"{f.Field}",
                NewObjectValue n => Children($"new#{n.Constructor.Method.Index} {n.Constructor}", n.Arguments),
                NewArrayValue a => Children($"new {a.ArrayType}", [a.Length]),
                ComposedValue c => Children($"struct {c.StructType}:{string.Join("/", c.Leaves.Select(l => string.Join(".", l.Path.Select(f => f.Field.Index))))}", c.Leaves.Select(l => l.Value)),
                BoxValue b => Children($"box {b.Boxed} {b.ObjectType}", [b.Operand]),
                IsInstValue i => Children($"isinst {i.Target}", [i.Operand]),
                CheckedCastValue c => Children($"castclass {c.Target}", [c.Operand]),
                FieldValue f => Children($"{f.Field}", [f.Receiver]),
                AddressValue a => Children("address", [a.Target]),
                IndirectValue i => Children("indirect", [i.Address]),
                ArrayLengthValue a => Children($"len {a.Type}/{a.Width}", [a.Array]),
                StringLengthValue s => Children("string-len", [s.String]),
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
            var last = prefix.FindLastIndex(s => values.IsOwnFieldStore(s));
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
                    ManagedStore s when values.IsOwnFieldStore(s) => Values(values.StorePath(s.Target), [s.Value]),
                    ManagedStore s => Values("store", [s.Target, s.Value]),
                    ManagedCall c => Values($"call#{c.Invocation.Method.Method.Index}:{c.Invocation.Method}:{c.Invocation.Virtual}",
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
        foreach (var store in prefix.Where(values.IsOwnFieldStore).Cast<ManagedStore>())
        {
            if (values.UsesArgument(store.Value, a => a.Index >= 0)) return "构造函数 字段初始化器引用了参数";
            if (Key(store.Value) is not { } key)
            {
                if (PrefixShape() is not { } prefixShape) return "构造函数 字段初始化器的值尚未支持比较";
                shape = prefixShape;
                return null;
            }
            initializers.Add($"{values.StorePath(store.Target)} = {key}");
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
            var part = values.IsOwnFieldStore(statement) || statement is ManagedAssignment a && initializerLocals.Contains(a.Target.Variable);
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
    /// 未写出的构造函数是骨架桩，无从知道它是否以 this(...) 链接，按不一致处理。返回源码形式不一致的构造函数。
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
