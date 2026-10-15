using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>以真实构造函数的完整方法体匹配分配后的内联片段；保留分配位置并输出构造依赖。</summary>
public static class InlineConstructors
{
    public static ManagedBody Recover(RecoverySession session, ManagedBody body)
    {
        for (var block = 0; block < body.Blocks.Count; block++)
            for (var index = 0; index < body.Blocks[block].Statements.Count; index++)
            {
                if (body.Blocks[block].Statements[index] is not ManagedAssignment { Value: ObjectAllocationValue allocation }) continue;
                foreach (var definition in allocation.ObjectType.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic))
                {
                    var method = new MethodRef(definition, allocation.ObjectType.Arguments, []);
                    if (session.Constructors.Prove(method) is not { } proof || Match(session.Types, body, block, index, proof) is not { } replaced) continue;
                    body = replaced;
                    break;
                }
            }
        return ObjectConstruction.Recover(body);
    }

    internal static ManagedBody? Match(ManagedTypes types, ManagedBody body, int blockIndex, int index, ConstructorProof proof)
    {
        var block = body.Blocks[blockIndex];
        var target = proof.Body.Method;
        if (block.Statements[index] is not ManagedAssignment { Value: ObjectAllocationValue allocation } allocated
            || target.Method.Name != ".ctor" || target.Method.IsStatic || target.DeclaringType != allocation.Type
            || ConstructorDelegations.Linear(types, proof.Body) is not { Count: > 1 } pattern
            || pattern[^1] is not ManagedReturn { Value: null }) return null;
        var count = pattern.Count - 1;
        if (index + count >= block.Statements.Count || !ManagedAccess.Method(types, body.Method.Method.Owner, target, allocation.Type)) return null;
        var source = block.Statements.Skip(index + 1).Take(count).ToArray();
        var internalVariables = source.SelectMany(s => s switch
        {
            ManagedAssignment a => new[] { a.Target.Variable }, ManagedCall { Result: { } r } => [r.Variable], _ => Array.Empty<Variable>(),
        }).ToHashSet();
        if (internalVariables.Contains(allocated.Target.Variable)) return null;
        var allValues = body.Blocks.SelectMany(b => b.Statements).SelectMany(ValueTree.Values).SelectMany(ValueTree.Walk).ToArray();
        var addressed = allValues.OfType<AddressValue>().Select(a => a.Target).ToHashSet();
        // 构造私有临时值不能在片段之外继续被使用，否则提取为调用会改变存储的生存期。
        for (var b = 0; b < body.Blocks.Count; b++)
            for (var s = 0; s < body.Blocks[b].Statements.Count; s++)
                if ((b != blockIndex || s <= index || s > index + count)
                    && ValueTree.Values(body.Blocks[b].Statements[s]).SelectMany(ValueTree.Walk).OfType<LocalValue>().Any(v => internalVariables.Contains(v.Variable))) return null;
        bool PrivateAddress(AddressValue address)
        {
            var value = address.Target;
            while (value is FieldValue field && types.Kind(field.Receiver.Type) == ValueKind.Struct) value = field.Receiver;
            return value is ArgumentValue or LocalValue or StackLocalValue;
        }
        var patternValues = pattern.SelectMany(ValueTree.Values).SelectMany(ValueTree.Walk).ToArray();
        if (patternValues.Any(v => v is StackLocalValue) || patternValues.OfType<AddressValue>().Any(PrivateAddress)) return null;
        var arguments = new ManagedValue?[target.Method.Parameters.Count];
        var locals = new Dictionary<Variable, LocalValue>();
        bool Captured(ManagedValue value) => value.Type is not ByRefRef && !addressed.Contains(value)
            && (value is ConstantValue or StringValue or ArgumentValue
                || value is LocalValue local && local != allocated.Target && !internalVariables.Contains(local.Variable));
        bool Bind(LocalValue expected, LocalValue actual)
        {
            if (expected.Type != actual.Type || expected.Width != actual.Width || locals.ContainsKey(expected.Variable)) return false;
            locals.Add(expected.Variable, actual); return true;
        }
        bool Values(IReadOnlyList<ManagedValue> expected, IReadOnlyList<ManagedValue> actual)
            => expected.Count == actual.Count && expected.Zip(actual).All(p => Value(p.First, p.Second));
        bool Invocation(ManagedInvocation expected, ManagedInvocation actual) => expected.Method == actual.Method
            && (expected.Receiver is { } receiver ? actual.Receiver is { } other && Value(receiver, other) : actual.Receiver is null)
            && Values(expected.Arguments, actual.Arguments);
        bool Value(ManagedValue expected, ManagedValue actual)
        {
            if (expected.Type != actual.Type || expected.Width != actual.Width) return false;
            if (expected is ArgumentValue { Index: -1 }) return actual == allocated.Target;
            if (expected is ArgumentValue { Index: >= 0 } argument)
            {
                if (!Captured(actual) || argument.Index >= arguments.Length) return false;
                if (arguments[argument.Index] is { } previous) return previous == actual;
                arguments[argument.Index] = actual; return true;
            }
            return (expected, actual) switch
            {
                (LocalValue e, LocalValue a) => locals.TryGetValue(e.Variable, out var mapped) && mapped == a,
                (ConstantValue e, ConstantValue a) => e.Bits == a.Bits,
                (StringValue e, StringValue a) => e.Text == a.Text,
                (TypeHandleValue e, TypeHandleValue a) => e.TargetType == a.TargetType,
                (DefaultValue, DefaultValue) or (ObjectAllocationValue, ObjectAllocationValue) => true,
                (FieldValue e, FieldValue a) => e.Field == a.Field && Value(e.Receiver, a.Receiver),
                (StaticFieldValue e, StaticFieldValue a) => e.Field == a.Field,
                (IndirectValue e, IndirectValue a) => Value(e.Address, a.Address),
                (AddressValue e, AddressValue a) => Value(e.Target, a.Target),
                (NewArrayValue e, NewArrayValue a) => Value(e.Length, a.Length),
                (ArrayLengthValue e, ArrayLengthValue a) => Value(e.Array, a.Array),
                (ArrayElementValue e, ArrayElementValue a) => Value(e.Array, a.Array) && Value(e.Index, a.Index),
                (BoxValue e, BoxValue a) => e.Initialization == a.Initialization && Value(e.Operand, a.Operand),
                (NewObjectValue e, NewObjectValue a) => e.Constructor == a.Constructor && Values(e.Arguments, a.Arguments),
                (InvocationValue e, InvocationValue a) => Invocation(e.Invocation, a.Invocation),
                (AggregateValue e, AggregateValue a) => e.Members.Count == a.Members.Count
                    && e.Members.Zip(a.Members).All(p => p.First.Path.SequenceEqual(p.Second.Path) && Value(p.First.Value, p.Second.Value)),
                (BinaryValue e, BinaryValue a) => e.Op == a.Op && Value(e.Left, a.Left) && Value(e.Right, a.Right),
                (UnaryValue e, UnaryValue a) => e.Op == a.Op && Value(e.Operand, a.Operand),
                (ConversionValue e, ConversionValue a) => e.Kind == a.Kind && Value(e.Operand, a.Operand),
                (ComparisonValue e, ComparisonValue a) => e.Condition == a.Condition && Value(e.Left, a.Left) && Value(e.Right, a.Right),
                (ChoiceValue e, ChoiceValue a) => Value(e.Condition, a.Condition) && Value(e.True, a.True) && Value(e.False, a.False),
                (BooleanValue e, BooleanValue a) => e.IsAnd == a.IsAnd && Value(e.Left, a.Left) && Value(e.Right, a.Right),
                (NegatedValue e, NegatedValue a) => Value(e.Operand, a.Operand),
                _ => false,
            };
        }
        for (var i = 0; i < count; i++)
        {
            var matches = (pattern[i], source[i]) switch
            {
                (ManagedAssignment e, ManagedAssignment a) => Value(e.Value, a.Value) && Bind(e.Target, a.Target),
                (ManagedStore e, ManagedStore a) => Value(e.Target, a.Target) && Value(e.Value, a.Value),
                (ManagedCall e, ManagedCall a) => (!a.Tail || i == count - 1 && index + count == block.Statements.Count - 1)
                    && Invocation(e.Invocation, a.Invocation)
                    && (e.Result is { } result ? a.Result is { } other && Bind(result, other) : a.Result is null),
                _ => false,
            };
            if (!matches) return null;
        }
        if (arguments.Any(a => a is null)) return null;
        var call = new ManagedCall(source[0].Address, new(target, allocated.Target, arguments.Select(a => a!).ToArray()), null, source[^1] is ManagedCall { Tail: true });
        return body with
        {
            Blocks = body.Blocks.Select((b, i) => i == blockIndex ? b with { Statements = [.. b.Statements.Take(index + 1), call, .. b.Statements.Skip(index + count + 1)] } : b).ToArray(),
            Constructors = [.. body.Constructors, proof],
        };
    }
}
