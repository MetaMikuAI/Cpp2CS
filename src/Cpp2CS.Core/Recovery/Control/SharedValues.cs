using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Control;

/// <summary>
/// 原生代码把累加的结果留在寄存器里复用，比如 offset += Write(ref bytes, offset, x)。下降把这种纯运算代入每个使用点，
/// 表达式的深度和文本量随使用次数按平方增长，写出器的递归和反编译器的内联都被拖慢。
/// 这里把重复出现的深整数运算放回局部：第一次使用之前赋值，之后读局部。不再被读的局部接着累加，反编译后就是 num += x。
/// 提取的运算不读内存、不会抛出，叶子是地址没有外流的整数局部、参数和常量，所以提前求值和复用都不改变语义；叶子被重新赋值后记录失效。
/// 局部沿单一前驱链传递：到达链上语句的路径都先经过前面的赋值。进出保护区的边不传递，finally 可能在中间改写叶子。
/// async 和迭代器的 MoveNext 不处理：反编译器按固定形态识别它们。内联证明用的方法体不经过这一步。
/// </summary>
internal static class SharedValues
{
    /// <summary>嵌套这么多层二元运算才算深；较浅的表达式留在原处更好读，只有深表达式的前缀才一起提取。</summary>
    private const int MinimumDepth = 3;
    /// <summary>赋值最多往前移这么多条语句；读取的局部写得更早时留在使用点，不让赋值离使用太远。</summary>
    private const int PlacementWindow = 16;

    /// <param name="extracted">写出的局部赋值数。</param>
    public static ManagedBody Run(ManagedBody body, ManagedTypes types, out int extracted)
    {
        extracted = 0;
        if (body.Method.Method.Name == "MoveNext" || !AnyDeep(body)) return body;
        return new Pass(body, types).Run(out extracted);
    }

    private static bool AnyDeep(ManagedBody body) => body.Blocks.SelectMany(b => b.Statements)
        .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).Any(v => Depth(v) >= MinimumDepth);

    private static int Depth(ManagedValue value)
    {
        var deepest = 0;
        foreach (var child in ManagedValues.Children(value)) deepest = Math.Max(deepest, Depth(child));
        return value is BinaryValue ? deepest + 1 : deepest;
    }

    /// <summary>结构相同的纯运算共用一个节点。子节点总是先于父节点建立。</summary>
    private sealed class Node(int id, int depth, int[] children, bool extractable)
    {
        public int Id { get; } = id;
        public int Depth { get; } = depth;
        public int[] Children { get; } = children;
        public bool Extractable { get; } = extractable;
        public List<int> Parents { get; } = [];
        /// <summary>出现次数；嵌在重复出现的父节点里的只算一次。</summary>
        public int Count { get; set; }
        /// <summary>还没有处理的出现次数，只用来判断局部能否接着累加。</summary>
        public int Pending { get; set; }
        public bool Worth { get; set; }
        /// <summary>上层值得提取，经转换传到下层。</summary>
        public bool Carried { get; set; }
        public bool ContainsWorth { get; set; }
    }

    private sealed class Pass
    {
        private readonly ManagedBody body;
        private readonly ManagedTypes types;
        private readonly HashSet<Variable> addressedLocals = [];
        private readonly HashSet<int> addressedArguments = [];
        private readonly List<Node> nodes = [];
        private readonly Dictionary<object, int> ids = [];
        private readonly Dictionary<ManagedValue, int> interned = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<Variable, List<int>> leaves = [];
        private readonly HashSet<Variable> created = [];
        /// <summary>当前语句里还要在语句执行时读取的新局部。赋值都排在语句之前，这些局部不能接着累加。</summary>
        private readonly Dictionary<Variable, int> reading = [];
        private int nextLocal;
        private int extracted;

        public Pass(ManagedBody body, ManagedTypes types)
        {
            this.body = body;
            this.types = types;
            foreach (var value in body.Blocks.SelectMany(b => b.Statements)
                .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk))
            {
                if (value is AddressValue { Target: LocalValue local }) addressedLocals.Add(local.Variable);
                if (value is AddressValue { Target: ArgumentValue argument }) addressedArguments.Add(argument.Index);
            }
        }

        public ManagedBody Run(out int count)
        {
            foreach (var value in body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))))
                Note(value);
            Mark();
            count = 0;
            if (!nodes.Any(n => n.Worth)) return body;
            nextLocal = EnumeratorForms.NextLocal(body);
            var rewritten = Rewrite();
            count = extracted;
            return body with { Blocks = body.Blocks.Select(b => rewritten.TryGetValue(b, out var statements) ? b with { Statements = statements } : b).ToArray() };
        }

        private bool Integer(ManagedValue value) => types.Kind(value.Type) == TypeKind.Int;

        private int Intern(ManagedValue value)
        {
            if (interned.TryGetValue(value, out var known)) return known;
            return interned[value] = Build(value);
        }

        private int Build(ManagedValue value)
        {
            switch (value)
            {
                case LocalValue local when Integer(local) && !addressedLocals.Contains(local.Variable):
                {
                    var id = Make(local, local, 0, []);
                    if (!leaves.TryGetValue(local.Variable, out var list)) leaves[local.Variable] = list = [];
                    if (!list.Contains(id)) list.Add(id);
                    return id;
                }
                case ArgumentValue argument when Integer(argument) && !addressedArguments.Contains(argument.Index):
                    return Make(argument, argument, 0, []);
                case ConstantValue constant when Integer(constant):
                    return Make(constant, constant, 0, []);
                case BinaryValue { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor or BinOp.Shl or BinOp.LShr or BinOp.AShr } binary when Integer(binary):
                {
                    var (left, right) = (Intern(binary.Left), Intern(binary.Right));
                    if (left < 0 || right < 0) return -1;
                    return Make((binary.Op, left, right, binary.Type, binary.Width), binary, Math.Max(nodes[left].Depth, nodes[right].Depth) + 1, [left, right]);
                }
                case UnaryValue { Op: UnOp.Neg or UnOp.Not } unary when Integer(unary):
                {
                    var operand = Intern(unary.Operand);
                    return operand < 0 ? -1 : Make((unary.Op, operand, unary.Type, unary.Width), unary, nodes[operand].Depth, [operand]);
                }
                case ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion when Integer(conversion):
                {
                    var operand = Intern(conversion.Operand);
                    return operand < 0 ? -1 : Make((conversion.Kind, operand, conversion.Type, conversion.Width), conversion, nodes[operand].Depth, [operand]);
                }
                default:
                    return -1;
            }
        }

        private int Make(object key, ManagedValue value, int depth, int[] children)
        {
            if (ids.TryGetValue(key, out var id)) return id;
            id = nodes.Count;
            nodes.Add(new Node(id, depth, children, value is BinaryValue { Width: 32 or 64 } && types.Bits(value.Type) == value.Width));
            foreach (var child in children) nodes[child].Parents.Add(id);
            ids[key] = id;
            return id;
        }

        private void Note(ManagedValue value)
        {
            var id = Intern(value);
            if (id >= 0) Bump(nodes[id]);
            else foreach (var child in ManagedValues.Children(value)) Note(child);
        }

        private void Bump(Node node)
        {
            if (node.Count++ > 0) return;
            foreach (var child in node.Children) Bump(nodes[child]);
        }

        /// <summary>深的重复运算值得提取，它重复出现的子运算也一起提取，累加链从头开始写成局部。</summary>
        private void Mark()
        {
            foreach (var node in Enumerable.Reverse(nodes))
            {
                node.Pending = node.Count;
                if (node.Extractable && node.Depth >= MinimumDepth && node.Count >= 2) node.Worth = true;
                if (!node.Worth && !node.Carried) continue;
                foreach (var child in node.Children.Select(c => nodes[c]))
                {
                    if (child.Extractable && child.Count >= 2) child.Worth = true;
                    else if (!child.Extractable) child.Carried = true;
                }
            }
            foreach (var node in nodes) node.ContainsWorth = node.Worth || node.Children.Any(c => nodes[c].ContainsWorth);
        }

        private Dictionary<ManagedBlock, IReadOnlyList<ManagedStatement>> Rewrite()
        {
            var blocks = body.Blocks.ToDictionary(b => b.Address);
            var incoming = new Dictionary<ulong, int>();
            foreach (var edge in body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges))
                incoming[edge.Target] = incoming.GetValueOrDefault(edge.Target) + 1;
            var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
            var scopes = new Dictionary<ulong, List<int>>();
            for (var i = 0; i < body.Regions.Count; i++)
                foreach (var address in body.Regions[i].Try.Concat(body.Regions[i].Handler))
                    (scopes.TryGetValue(address, out var list) ? list : scopes[address] = []).Add(i);
            bool Continues(ManagedBlock from, ulong to) => blocks.ContainsKey(to) && incoming.GetValueOrDefault(to) == 1 && !entries.Contains(to)
                && (scopes.GetValueOrDefault(from.Address) ?? []).SequenceEqual(scopes.GetValueOrDefault(to) ?? []);
            var continuations = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Where(e => Continues(b, e.Target)).Select(e => e.Target)).ToHashSet();

            var rewritten = new Dictionary<ManagedBlock, IReadOnlyList<ManagedStatement>>(ReferenceEqualityComparer.Instance);
            var work = new Stack<(ManagedBlock Block, Dictionary<int, LocalValue> Available)>();
            foreach (var block in body.Blocks.Where(b => !continuations.Contains(b.Address))) work.Push((block, []));
            while (work.TryPop(out var item))
            {
                var (block, available) = item;
                var output = new List<ManagedStatement>(block.Statements.Count);
                foreach (var statement in block.Statements)
                {
                    reading.Clear();
                    var mapped = ManagedValues.Map(statement, value => Rewrite(value, available, output, statement.Address));
                    output.Add(mapped);
                    foreach (var defined in Definitions(mapped)) Kill(defined.Variable, available);
                }
                rewritten[block] = output;
                ManagedEdge[] edges = block.Statements.Count == 0 ? [] : ManagedValues.Edges(block.Statements[^1]).Where(e => Continues(block, e.Target)).ToArray();
                for (var i = 0; i < edges.Length; i++)
                {
                    var next = i == edges.Length - 1 ? available : new Dictionary<int, LocalValue>(available);
                    foreach (var copy in edges[i].Copies) Kill(copy.Target.Variable, next);
                    work.Push((blocks[edges[i].Target], next));
                }
            }
            return rewritten;
        }

        private ManagedValue Rewrite(ManagedValue value, Dictionary<int, LocalValue> available, List<ManagedStatement> output, ulong address)
        {
            ManagedValue Child(ManagedValue child) => Rewrite(child, available, output, address);
            var id = Intern(value);
            if (id < 0) return ManagedValues.Map(value, Child);
            var node = nodes[id];
            if (!node.ContainsWorth) return value;
            if (available.TryGetValue(id, out var known))
            {
                node.Pending--;
                Reading(known, 1);
                return known;
            }
            if (!node.Worth) return ManagedValues.Map(value, Child);
            node.Pending--;
            var rebuilt = (BinaryValue)ManagedValues.Map(value, Child);
            return Extract(node, rebuilt, available, output, address);
        }

        private LocalValue Extract(Node node, BinaryValue value, Dictionary<int, LocalValue> available, List<ManagedStatement> output, ulong address)
        {
            // 这个值的读取随赋值提前完成，不再算作语句执行时的读取。
            foreach (var read in ManagedValues.Walk(value).OfType<LocalValue>().Where(l => created.Contains(l.Variable))) Reading(read, -1);
            var (left, right) = (node.Children[0], node.Children[1]);
            LocalValue target;
            if (value.Op is BinOp.Add or BinOp.Mul or BinOp.And or BinOp.Or or BinOp.Xor && Finished(value.Right, right, value, available) is { } accumulated)
            {
                value = value with { Left = accumulated, Right = value.Left };
                target = accumulated;
                available.Remove(right);
            }
            else if (Finished(value.Left, left, value, available) is { } reused)
            {
                target = reused;
                available.Remove(left);
            }
            else
            {
                target = new LocalValue(new Variable(Storage.Temp(nextLocal++), 1), value.Type, value.Width);
                created.Add(target.Variable);
            }
            output.Insert(Placement(output, target, value), new ManagedAssignment(address, target, value));
            available[node.Id] = target;
            extracted++;
            Reading(target, 1);
            return target;
        }

        /// <summary>
        /// 赋值放在它读取的局部最后一次写入之后，而不是紧贴使用点：插在使用点之前会隔开反编译器要内联的相邻赋值。
        /// 运算是纯的，只要不越过这些写入和目标局部的读写就不改变语义。
        /// </summary>
        private static int Placement(List<ManagedStatement> output, LocalValue target, ManagedValue value)
        {
            var reads = ManagedValues.Walk(value).OfType<LocalValue>().Select(l => l.Variable).Append(target.Variable).ToHashSet();
            var at = output.Count;
            for (; at > 0 && output.Count - at < PlacementWindow; at--)
            {
                var previous = output[at - 1];
                if (Definitions(previous).Any(d => reads.Contains(d.Variable))
                    || ManagedValues.Of(previous).SelectMany(ManagedValues.Walk).OfType<LocalValue>().Any(l => l.Variable.Equals(target.Variable))) return at;
            }
            return at == 0 ? 0 : output.Count;
        }

        private void Reading(LocalValue local, int change) => reading[local.Variable] = reading.GetValueOrDefault(local.Variable) + change;

        /// <summary>这里提取出来的局部已经没有其他读者时，可以接着用来存放新值。</summary>
        private LocalValue? Finished(ManagedValue operand, int id, BinaryValue value, Dictionary<int, LocalValue> available) =>
            operand is LocalValue local && created.Contains(local.Variable) && nodes[id].Pending <= 0 && reading.GetValueOrDefault(local.Variable) == 0
            && available.TryGetValue(id, out var held) && held.Variable.Equals(local.Variable)
            && local.Type.Equals(value.Type) && local.Width == value.Width ? local : null;

        private void Kill(Variable variable, Dictionary<int, LocalValue> available)
        {
            if (available.Count == 0 || !leaves.TryGetValue(variable, out var list)) return;
            var seen = new HashSet<int>();
            var work = new Stack<int>(list);
            while (work.TryPop(out var id))
            {
                if (!seen.Add(id)) continue;
                available.Remove(id);
                foreach (var parent in nodes[id].Parents) work.Push(parent);
            }
        }

        private static IEnumerable<LocalValue> Definitions(ManagedStatement statement) => statement switch
        {
            ManagedAssignment a => [a.Target],
            ManagedCall { Result: { } result } => [result],
            ManagedAwait { Result: { } result } => [result],
            _ => [],
        };
    }
}
