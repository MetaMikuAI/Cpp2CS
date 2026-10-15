using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>用已验证的访问器替换不可直接访问的字段。读取留在原表达式位置；值类型写入路径不改成副本。</summary>
public static class InlineAccessors
{
    public static ManagedBody Recover(RecoverySession session, ManagedBody body)
        => Recover(session.Types, body, session.Accessors.Find);

    internal static ManagedBody Recover(ManagedTypes types, ManagedBody body, Func<FieldValue, bool, TypeDef, AccessorProof?> find)
    {
        var uses = new List<AccessorUse>();
        var caller = body.Method.Method.Owner;

        ManagedValue Value(ManagedValue value, ulong address, bool needsAddress = false)
        {
            switch (value)
            {
                case FieldValue field:
                {
                    var receiverNeedsAddress = needsAddress && types.Kind(field.Receiver.Type) == ValueKind.Struct;
                    var rewritten = field with { Receiver = Value(field.Receiver, address, receiverNeedsAddress) };
                    if (!needsAddress && !ManagedAccess.Field(types, caller, field.Field, field.Receiver.Type)
                        && find(field, false, caller) is { } proof)
                    {
                        uses.Add(new(address, proof));
                        return new InvocationValue(new ManagedInvocation(proof.Method, rewritten.Receiver, []), field.Type, field.Width);
                    }
                    return rewritten;
                }
                case IndirectValue indirect: return indirect with { Address = Value(indirect.Address, address) };
                case AddressValue reference: return reference with { Target = Value(reference.Target, address, needsAddress: true) };
                case AggregateValue aggregate: return aggregate with { Members = aggregate.Members.Select(m => m with { Value = Value(m.Value, address) }).ToArray() };
                case BinaryValue binary: return binary with { Left = Value(binary.Left, address), Right = Value(binary.Right, address) };
                case UnaryValue unary: return unary with { Operand = Value(unary.Operand, address) };
                case ConversionValue conversion: return conversion with { Operand = Value(conversion.Operand, address) };
                case ComparisonValue comparison: return comparison with { Left = Value(comparison.Left, address), Right = Value(comparison.Right, address) };
                case ChoiceValue choice: return choice with { Condition = Value(choice.Condition, address), True = Value(choice.True, address, needsAddress), False = Value(choice.False, address, needsAddress) };
                case BooleanValue boolean: return boolean with { Left = Value(boolean.Left, address), Right = Value(boolean.Right, address) };
                case NegatedValue negated: return negated with { Operand = Value(negated.Operand, address) };
                case InvocationValue invocation: return invocation with { Invocation = Invocation(invocation.Invocation, address) };
                default: return value;
            }
        }

        ManagedInvocation Invocation(ManagedInvocation invocation, ulong address) => invocation with
        {
            Receiver = invocation.Receiver is { } receiver ? Value(receiver, address, types.Kind(receiver.Type) == ValueKind.Struct) : null,
            Arguments = invocation.Arguments.Select(v => Value(v, address, v.Type is ByRefRef)).ToArray(),
        };

        ManagedEdge Edge(ManagedEdge edge, ulong address) => edge with
        {
            Copies = edge.Copies.Select(c => c with { Value = Value(c.Value, address) }).ToArray(),
        };

        ManagedStatement Statement(ManagedStatement statement)
        {
            var address = statement.Address;
            switch (statement)
            {
                case ManagedAssignment assignment: return assignment with { Value = Value(assignment.Value, address) };
                case ManagedStore store:
                {
                    var target = Value(store.Target, address, needsAddress: true);
                    var stored = Value(store.Value, address);
                    if (target is FieldValue field && !ManagedAccess.Field(types, caller, field.Field, field.Receiver.Type)
                        && find(field, true, caller) is { } proof)
                    {
                        uses.Add(new(address, proof));
                        return new ManagedCall(address, new ManagedInvocation(proof.Method, field.Receiver, [stored]), null, false);
                    }
                    return store with { Target = target, Value = stored };
                }
                case ManagedCall call: return call with { Invocation = Invocation(call.Invocation, address) };
                case ManagedReturn returned: return returned with { Value = returned.Value is { } value ? Value(value, address) : null };
                case ManagedJump jump: return jump with { Edge = Edge(jump.Edge, address) };
                case ManagedBranch branch: return branch with
                {
                    Condition = Value(branch.Condition, address), Taken = Edge(branch.Taken, address), Fallthrough = Edge(branch.Fallthrough, address),
                };
                default: throw new NotSupportedException(statement.ToString());
            }
        }

        var blocks = body.Blocks.Select(b => b with { Statements = b.Statements.Select(Statement).ToArray() }).ToArray();
        return body with { Blocks = blocks, Accessors = [.. body.Accessors, .. uses] };
    }
}
