using Cpp2CS.Ir;
using Cpp2CS.Managed;

namespace Cpp2CS.Output;

/// <summary>沿可达控制流验证 this 初始化；元数据准备、独立参数计算和本类字段初始化可以先于基类调用。</summary>
internal static class ConstructorInitialization
{
    public static string? Check(ManagedBody body)
    {
        var owner = body.Method.Method.Owner;
        var definitions = new Dictionary<Variable, List<ManagedValue>>();
        void Define(LocalValue local, ManagedValue value)
        {
            if (!definitions.TryGetValue(local.Variable, out var values)) definitions.Add(local.Variable, values = []);
            values.Add(value);
        }
        IEnumerable<ManagedEdge> Edges(ManagedStatement statement) => statement switch
        {
            ManagedJump jump => [jump.Edge], ManagedBranch branch => [branch.Taken, branch.Fallthrough], _ => [],
        };
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment assignment) Define(assignment.Target, assignment.Value);
            foreach (var copy in Edges(statement).SelectMany(e => e.Copies)) Define(copy.Target, copy.Value);
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
        bool UsesThis(ManagedValue value)
        {
            var pending = new Stack<ManagedValue>(); pending.Push(value);
            var seen = new HashSet<Variable>();
            while (pending.TryPop(out var current))
            {
                if (current is ArgumentValue { Index: -1 }) return true;
                if (current is LocalValue local && seen.Add(local.Variable) && definitions.TryGetValue(local.Variable, out var sources))
                    foreach (var source in sources) pending.Push(source);
                foreach (var child in Children(current)) pending.Push(child);
            }
            return false;
        }
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var queue = new Queue<(ulong Address, bool Initialized)>();
        queue.Enqueue((body.Blocks[0].Address, false));
        var visited = new HashSet<(ulong, bool)>();
        while (queue.TryDequeue(out var state))
        {
            if (!visited.Add(state)) continue;
            var initialized = state.Initialized;
            foreach (var statement in blocks[state.Address].Statements)
            {
                if (statement is ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: { } receiver } } call && IsThis(receiver))
                {
                    var target = call.Invocation.Method;
                    if (initialized) return "构造函数路径重复初始化 this";
                    if (target.Method.IsStatic || target.Method.Owner != owner && target.DeclaringType != owner.BaseType)
                        return "构造函数没有调用本类或直接基类构造函数";
                    if (call.Invocation.Arguments.Any(UsesThis)) return "基类构造参数使用了未初始化的 this";
                    initialized = true;
                }
                else if (!initialized)
                {
                    var permitted = statement switch
                    {
                        ManagedAssignment a => IsThis(a.Value) || !UsesThis(a.Value),
                        ManagedStore { Target: FieldValue f } s when IsThis(f.Receiver) && f.Field.Field.Owner == owner => !UsesThis(s.Value),
                        ManagedStore s => !UsesThis(s.Target) && !UsesThis(s.Value),
                        ManagedCall c => (c.Invocation.Receiver is null || !UsesThis(c.Invocation.Receiver)) && !c.Invocation.Arguments.Any(UsesThis),
                        ManagedJump => true,
                        ManagedBranch b => !UsesThis(b.Condition),
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
        return null;
    }

    private static IEnumerable<ManagedValue> Children(ManagedValue value) => value switch
    {
        AddressValue a => [a.Target], AggregateValue a => a.Members.Select(m => m.Value),
        FieldValue f => [f.Receiver], IndirectValue i => [i.Address],
        InvocationValue i => i.Invocation.Receiver is { } receiver ? new[] { receiver }.Concat(i.Invocation.Arguments) : i.Invocation.Arguments,
        NewArrayValue a => [a.Length], ArrayLengthValue a => [a.Array], ArrayElementValue a => [a.Array, a.Index],
        BinaryValue b => [b.Left, b.Right], UnaryValue u => [u.Operand], ConversionValue c => [c.Operand],
        ComparisonValue c => [c.Left, c.Right], ChoiceValue c => [c.Condition, c.True, c.False],
        BooleanValue b => [b.Left, b.Right], NegatedValue n => [n.Operand],
        ArgumentValue or LocalValue or StackLocalValue or DefaultValue or ConstantValue or StringValue or TypeHandleValue or StaticFieldValue => [],
        _ => throw new NotSupportedException(value.ToString()),
    };
}
