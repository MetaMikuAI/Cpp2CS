using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>沿正常边传播非空或空值事实；重新赋值和取址不沿用旧事实。</summary>
internal static class SourceNonNullReceivers
{
    internal static ManagedBody FoldBranches(ManagedBody body)
    {
        var present = Read(body, null);
        var absent = ReadNull(body);
        return body with
        {
            Blocks = body.Blocks.Select(b => b with
            {
                Statements = b.Statements.Select(s =>
        {
            if (s is not ManagedBranch branch) return s;
            if (branch.Condition is ConstantValue constant) return new ManagedJump(s.Address, constant.Bits != 0 ? branch.Taken : branch.Fallthrough);
            if (branch.Condition is not ComparisonValue { Condition: Cond.Eq or Cond.Ne } condition) return s;
            bool Known(Dictionary<ManagedStatement, HashSet<ManagedValue>> facts, ManagedValue value, ManagedValue zero)
                => zero is ConstantValue { Bits: 0 } && facts[s].Contains(value);
            bool? nonnull = Known(present, condition.Left, condition.Right) || Known(present, condition.Right, condition.Left) ? true
                : Known(absent, condition.Left, condition.Right) || Known(absent, condition.Right, condition.Left) ? false : null;
            return nonnull is { } known ? new ManagedJump(s.Address, known == (condition.Condition == Cond.Ne) ? branch.Taken : branch.Fallthrough) : s;
        }).ToArray()
            }).ToArray()
        };
    }

    internal static Dictionary<ManagedStatement, HashSet<ManagedValue>> Read(ManagedBody body, Func<MethodRef, bool>? getter)
        => Read(body, getter, false);

    internal static Dictionary<ManagedStatement, HashSet<ManagedValue>> ReadNull(ManagedBody body) => Read(body, null, true);

    internal static ManagedBody FoldBooleans(ManagedBody body, ManagedTypes types)
    {
        var whenTrue = Read(body, null, false, types);
        var whenFalse = Read(body, null, true, types);
        return body with
        {
            Blocks = body.Blocks.Select(block => block with
            {
                Statements = block.Statements.Select(statement =>
        {
            ManagedValue Replace(ManagedValue value) => whenTrue[statement].Contains(value) ? new ConstantValue(1, value.Type, value.Width)
                : whenFalse[statement].Contains(value) ? new ConstantValue(0, value.Type, value.Width) : ManagedValues.Map(value, Replace);
            return ManagedValues.Map(statement, Replace, target => ManagedValues.Map(target, Replace));
        }).ToArray()
            }).ToArray()
        };
    }

    private static Dictionary<ManagedStatement, HashSet<ManagedValue>> Read(ManagedBody body, Func<MethodRef, bool>? getter, bool nullOnly,
        ManagedTypes? booleans = null)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var addressed = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).ToHashSet();
        bool TrackedType(ManagedValue value) => booleans is null ? ManagedTypes.IsReferenceType(value.Type) : booleans.Kind(value.Type) == TypeKind.Bool;
        bool Track(ManagedValue value) => value is LocalValue or ArgumentValue && TrackedType(value) && !addressed.Contains(value);
        bool Constant(ManagedValue value) => value is ConstantValue constant && TrackedType(value)
            && (nullOnly ? constant.Bits == 0 : booleans is not null && constant.Bits == 1);
        void Transfer(HashSet<ManagedValue> known, ManagedStatement statement)
        {
            void Read(ManagedValue value)
            {
                if (!nullOnly && value is FieldValue field && Track(field.Receiver)) known.Add(field.Receiver);
                if (value is ChoiceValue choice) { Read(choice.Condition); return; }
                if (value is BooleanValue boolean) { Read(boolean.Left); return; }
                ManagedValues.Map(value, child => { Read(child); return child; });
            }
            foreach (var value in ManagedValues.Of(statement)) Read(value);
            if (statement is ManagedCheck { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne } check })
            {
                var checkedValue = check.Right is ConstantValue { Bits: 0 } ? check.Left
                    : check.Left is ConstantValue { Bits: 0 } ? check.Right : null;
                if (checkedValue is not null && Track(checkedValue))
                {
                    if (nullOnly == (check.Condition == Cond.Ne)) known.Add(checkedValue);
                    else known.Remove(checkedValue);
                }
            }
            if (!nullOnly && statement is ManagedCall { Invocation: var invocation } && (invocation.Virtual || getter?.Invoke(invocation.Method) == true)
                && invocation.Receiver is { } receiver && Track(receiver)) known.Add(receiver);
            ManagedValue? target = statement switch
            {
                ManagedAssignment assignment => assignment.Target,
                ManagedCall call => call.Result,
                ManagedAwait awaited => awaited.Result,
                ManagedStore { Target: LocalValue or ArgumentValue } store => store.Target,
                _ => null,
            };
            if (target is null) return;
            var source = statement switch { ManagedAssignment copy => copy.Value, ManagedStore store => store.Value, _ => null };
            var proven = source is not null && (known.Contains(source) || Constant(source)
                || !nullOnly && booleans is null && source is NewObjectValue or NewArrayValue or DelegateValue or StringValue);
            known.Remove(target);
            if (proven && Track(target)) known.Add(target);
        }
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        HashSet<ManagedValue> Edge(HashSet<ManagedValue> input, ulong predecessor, ManagedEdge edge)
        {
            var output = input.ToHashSet();
            if (booleans is not null && blocks[predecessor].Statements.LastOrDefault() is ManagedBranch booleanBranch
                && !ReferenceEquals(booleanBranch.Taken, booleanBranch.Fallthrough))
            {
                var value = booleanBranch.Condition is NegatedValue negated ? negated.Operand : booleanBranch.Condition;
                if (Track(value))
                {
                    var isFalse = ReferenceEquals(booleanBranch.Fallthrough, edge) ^ (booleanBranch.Condition is NegatedValue);
                    if (isFalse == nullOnly) output.Add(value); else output.Remove(value);
                }
            }
            if (blocks[predecessor].Statements.LastOrDefault() is ManagedBranch { Condition: ComparisonValue { Condition: Cond.Eq or Cond.Ne } condition } branch
                && !ReferenceEquals(branch.Taken, branch.Fallthrough))
            {
                var value = condition.Right is ConstantValue { Bits: 0 } ? condition.Left
                    : condition.Left is ConstantValue { Bits: 0 } ? condition.Right : null;
                if (value is not null && Track(value))
                {
                    var isNull = ReferenceEquals(branch.Taken, edge) == (condition.Condition == Cond.Eq);
                    if (isNull == nullOnly) output.Add(value); else output.Remove(value);
                }
            }
            var beforeCopies = output.ToHashSet();
            foreach (var copy in edge.Copies) output.Remove(copy.Target);
            foreach (var copy in edge.Copies)
                if (Track(copy.Target) && (beforeCopies.Contains(copy.Value) || Constant(copy.Value))) output.Add(copy.Target);
            return output;
        }
        var incoming = body.Blocks.SelectMany(b => b.Statements.SelectMany(ManagedValues.Edges).Select(e => (Block: b.Address, Edge: e)))
            .GroupBy(p => p.Edge.Target).ToDictionary(g => g.Key, g => g.ToArray());
        var entries = body.Regions.Select(r => r.HandlerEntry).Append(body.Blocks[0].Address).ToHashSet();
        var inputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>());
        var outputs = body.Blocks.ToDictionary(b => b.Address, _ => new HashSet<ManagedValue>());
        bool changed;
        do
        {
            changed = false;
            foreach (var block in body.Blocks)
            {
                var state = new HashSet<ManagedValue>();
                if (!entries.Contains(block.Address) && incoming.TryGetValue(block.Address, out var predecessors))
                {
                    state = Edge(outputs[predecessors[0].Block], predecessors[0].Block, predecessors[0].Edge);
                    foreach (var predecessor in predecessors.Skip(1)) state.IntersectWith(Edge(outputs[predecessor.Block], predecessor.Block, predecessor.Edge));
                }
                inputs[block.Address] = state.ToHashSet();
                foreach (var statement in block.Statements) Transfer(state, statement);
                if (outputs[block.Address].SetEquals(state)) continue;
                outputs[block.Address] = state; changed = true;
            }
        } while (changed);
        var result = new Dictionary<ManagedStatement, HashSet<ManagedValue>>(ReferenceEqualityComparer.Instance);
        foreach (var block in body.Blocks)
        {
            var state = inputs[block.Address].ToHashSet();
            foreach (var statement in block.Statements)
            {
                result[statement] = state.ToHashSet();
                Transfer(state, statement);
            }
        }
        return result;
    }
}
