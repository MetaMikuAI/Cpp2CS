using System.Reflection;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>候选构造函数的完整方法体与地址；替换内联片段时必须一并写出该实现。</summary>
public sealed record ConstructorProof(ulong Address, ManagedBody Body);

/// <summary>按完整构造后缀恢复被内联的 this(...) 调用，不移动参数求值或基类初始化。</summary>
public sealed class ConstructorDelegations(RecoverySession session)
{
    private readonly Dictionary<MethodRef, ConstructorProof?> proofs = new();

    public ManagedBody Recover(ManagedBody body)
    {
        if (Linear(session.Types, body) is not { } statements) return body;
        var start = Initialization(statements);
        if (start <= 0 || !statements.Take(start).OfType<ManagedCall>().Any()) return body;
        foreach (var definition in body.Method.Method.Owner.Methods)
        {
            if (definition == body.Method.Method || definition.Name != ".ctor" || definition.IsStatic) continue;
            var method = new MethodRef(definition, body.Method.TypeArguments, []);
            if (Prove(method) is { } proof && Match(session.Types, body, proof) is { } rewritten) return rewritten;
        }
        return body;
    }

    private ConstructorProof? Prove(MethodRef method)
    {
        if (proofs.TryGetValue(method, out var cached)) return cached;
        proofs[method] = null;
        var definition = method.Method;
        if (method.TypeArguments.Count != 0 || definition.Owner.GenericParameters.Count != 0
            || definition.GenericParameters.Count != 0 || definition.IsAbstract
            || (definition.ImplAttributes & MethodImplAttributes.Synchronized) != 0) return null;
        var address = definition.Address;
        if (address == 0 || !session.Model.Code.TryGetValue(address, out var owners) || !owners.Any(o => o.Method == method)
            || session.Functions.At(address) is not { } range || range.Start != address) return null;
        var recovered = BodyRecovery.Recover(session, session.Analyze(method, address, range), recoverAccessors: false, recoverConstructors: false);
        if (recovered.Body is not { } body || Linear(session.Types, body) is not { } statements || Initialization(statements) != 0
            || ((ManagedCall)statements[0]).Invocation.Method.DeclaringType != definition.Owner.BaseType) return null;
        return proofs[method] = new(address, body);
    }

    internal static ManagedBody? Match(ManagedTypes types, ManagedBody body, ConstructorProof proof)
    {
        var target = proof.Body.Method;
        if (target.Method == body.Method.Method || target.Method.Name != ".ctor" || target.Method.IsStatic || target.Method.Owner != body.Method.Method.Owner
            || Linear(types, body) is not { } source || Linear(types, proof.Body) is not { } pattern) return null;
        var start = Initialization(source);
        if (start <= 0 || Initialization(pattern) != 0 || source.Count - start != pattern.Count
            || ((ManagedCall)pattern[0]).Invocation.Method.DeclaringType != target.Method.Owner.BaseType
            || !source.Take(start).OfType<ManagedCall>().Any()) return null;
        var before = source.Take(start).OfType<ManagedAssignment>().Select(a => a.Target.Variable)
            .Concat(source.Take(start).OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)).ToHashSet();
        var arguments = new ManagedValue?[target.Method.Parameters.Count];
        bool Value(ManagedValue expected, ManagedValue actual)
        {
            if (expected.Type != actual.Type || expected.Width != actual.Width) return false;
            if (expected is ArgumentValue { Index: >= 0 } argument)
            {
                // 仅把已在片段之前求好的值作为调用参数，不能提前字段读取、装箱或其他有副作用的计算。
                if (actual is ArgumentValue { Index: -1 }) return false;
                if (actual is not (ArgumentValue or ConstantValue or StringValue)
                    && (actual is not LocalValue local || !before.Contains(local.Variable))) return false;
                if (arguments[argument.Index] is { } previous) return previous == actual;
                arguments[argument.Index] = actual;
                return true;
            }
            return (expected, actual) switch
            {
                (ArgumentValue { Index: -1 }, ArgumentValue { Index: -1 }) => true,
                (ConstantValue a, ConstantValue b) => a.Bits == b.Bits,
                (StringValue a, StringValue b) => a.Text == b.Text,
                (ConversionValue a, ConversionValue b) => a.Kind == b.Kind && Value(a.Operand, b.Operand),
                (FieldValue a, FieldValue b) => a.Field == b.Field && Value(a.Receiver, b.Receiver),
                _ => false,
            };
        }
        bool Call(ManagedCall expected, ManagedCall actual) => expected.Result is null && actual.Result is null
            && expected.Invocation.Method == actual.Invocation.Method && expected.Invocation.Receiver is { } receiver
            && actual.Invocation.Receiver is { } actualReceiver && Value(receiver, actualReceiver)
            && expected.Invocation.Arguments.Count == actual.Invocation.Arguments.Count
            && expected.Invocation.Arguments.Zip(actual.Invocation.Arguments).All(p => Value(p.First, p.Second));
        for (var i = 0; i < pattern.Count; i++)
        {
            var matches = (pattern[i], source[start + i]) switch
            {
                (ManagedCall expected, ManagedCall actual) when i == 0 => Call(expected, actual),
                (ManagedStore { Target: FieldValue { Receiver: ArgumentValue { Index: -1 } } } expected, ManagedStore actual) =>
                    Value(expected.Target, actual.Target) && Value(expected.Value, actual.Value),
                (ManagedReturn { Value: null }, ManagedReturn { Value: null }) when i == pattern.Count - 1 => true,
                _ => false,
            };
            if (!matches) return null;
        }
        if (arguments.Any(a => a is null)) return null;
        var invocation = new ManagedInvocation(target, new ArgumentValue(-1, "this", body.Method.DeclaringType, 64), arguments.Select(a => a!).ToArray());
        if (!ManagedAccess.Method(types, body.Method.Method.Owner, target, body.Method.DeclaringType)) return null;
        return body with
        {
            Blocks = [new(body.Blocks[0].Address, [.. source.Take(start), new ManagedCall(source[start].Address, invocation, null, false), source[^1]])],
            Constructors = [.. body.Constructors, proof],
        };
    }

    private static int Initialization(IReadOnlyList<ManagedStatement> statements)
    {
        for (var i = 0; i < statements.Count; i++)
            if (statements[i] is ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 } } }) return i;
        return -1;
    }

    /// <summary>只处理无分支、无回边、无边赋值的路径；展开参数与常量副本，不展开读取和调用结果。</summary>
    private static List<ManagedStatement>? Linear(ManagedTypes types, ManagedBody body)
    {
        if (body.Method.Method.Name != ".ctor" || body.Method.Method.IsStatic || body.Blocks.Count == 0) return null;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var visited = new HashSet<ulong>();
        var result = new List<ManagedStatement>();
        var aliases = new Dictionary<Variable, ManagedValue>();
        var changedStorage = false;
        ManagedValue Address(AddressValue value)
        {
            changedStorage |= Expand(value.Target) != value.Target;
            return value;
        }
        ManagedValue Expand(ManagedValue value) => value switch
        {
            LocalValue local when aliases.TryGetValue(local.Variable, out var source) => source,
            ConversionValue c => c with { Operand = Expand(c.Operand) },
            FieldValue f => f with { Receiver = Expand(f.Receiver) },
            IndirectValue i => i with { Address = Expand(i.Address) },
            AddressValue a => Address(a),
            AggregateValue a => a with { Members = a.Members.Select(m => m with { Value = Expand(m.Value) }).ToArray() },
            InvocationValue i => i with { Invocation = i.Invocation with
            {
                Receiver = i.Invocation.Receiver is { } receiver ? Expand(receiver) : null,
                Arguments = i.Invocation.Arguments.Select(Expand).ToArray(),
            } },
            NewArrayValue a => a with { Length = Expand(a.Length) },
            ArrayLengthValue a => a with { Array = Expand(a.Array) },
            ArrayElementValue a => a with { Array = Expand(a.Array), Index = Expand(a.Index) },
            BinaryValue b => b with { Left = Expand(b.Left), Right = Expand(b.Right) },
            UnaryValue u => u with { Operand = Expand(u.Operand) },
            ComparisonValue c => c with { Left = Expand(c.Left), Right = Expand(c.Right) },
            ChoiceValue c => c with { Condition = Expand(c.Condition), True = Expand(c.True), False = Expand(c.False) },
            BooleanValue b => b with { Left = Expand(b.Left), Right = Expand(b.Right) },
            NegatedValue n => n with { Operand = Expand(n.Operand) },
            ArgumentValue or LocalValue or StackLocalValue or DefaultValue or ConstantValue or StringValue or TypeHandleValue => value,
            _ => throw new NotSupportedException(value.ToString()),
        };
        bool Copy(ManagedValue value) => types.Kind(value.Type) != ValueKind.Struct
            && (value is ArgumentValue or ConstantValue or StringValue || value is ConversionValue c && Copy(c.Operand));
        var address = body.Blocks[0].Address;
        while (visited.Add(address))
        {
            foreach (var statement in blocks[address].Statements)
            {
                switch (statement)
                {
                    case ManagedAssignment a when Copy(Expand(a.Value)):
                        aliases.Add(a.Target.Variable, Expand(a.Value)); break;
                    case ManagedAssignment a: result.Add(a with { Value = Expand(a.Value) }); break;
                    case ManagedStore s: result.Add(s with { Target = Expand(s.Target), Value = Expand(s.Value) }); break;
                    case ManagedCall c:
                        result.Add(c with { Invocation = c.Invocation with
                        {
                            Receiver = c.Invocation.Receiver is { } receiver ? Expand(receiver) : null,
                            Arguments = c.Invocation.Arguments.Select(Expand).ToArray(),
                        }, Tail = false });
                        if (c.Tail) result.Add(new ManagedReturn(c.Address, null));
                        break;
                    case ManagedReturn { Value: null }: result.Add(statement); break;
                    case ManagedJump { Edge.Copies.Count: 0 }: break;
                    default: return null;
                }
            }
            if (blocks[address].Statements.LastOrDefault() is ManagedJump jump) { address = jump.Edge.Target; continue; }
            return !changedStorage && visited.Count == blocks.Count && result.LastOrDefault() is ManagedReturn ? result : null;
        }
        return null;
    }
}
