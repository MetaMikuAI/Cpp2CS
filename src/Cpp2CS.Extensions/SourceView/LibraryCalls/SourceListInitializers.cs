using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

internal static partial class SourceListCalls
{
    // 新 List 的初始化区没有外部观察者；容量分支两臂必须产生完全相同的 Add 序列。
    private static ManagedBody? MatchInitializer(ManagedBody body, ManagedTypes types, Action<ulong, MethodRef> matched)
    {
        if (body.Regions.Count != 0) return null;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var definitions = new Dictionary<Variable, List<ManagedValue>>();
        void Define(LocalValue local, ManagedValue value)
        {
            if (!definitions.TryGetValue(local.Variable, out var values)) definitions[local.Variable] = values = [];
            values.Add(value);
        }
        foreach (var statement in body.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is ManagedAssignment a) Define(a.Target, a.Value);
            foreach (var copy in ManagedValues.Edges(statement).SelectMany(e => e.Copies)) Define(copy.Target, copy.Value);
        }
        foreach (var startBlock in body.Blocks)
            for (var start = 0; start < startBlock.Statements.Count; start++)
            {
                if (startBlock.Statements[start] is not ManagedAssignment { Value: NewObjectValue { Arguments.Count: 0 } created } allocation
                    || created.Type is not DefinitionRef { Definition: { Assembly: "mscorlib.dll", FullName: "System.Collections.Generic.List" }, Arguments.Count: 1 } owner) continue;
                var list = allocation.Target;
                bool Origin(ManagedValue value, Func<ManagedValue, bool> terminal, HashSet<Variable> seen)
                {
                    value = Strip(value);
                    if (terminal(value)) return true;
                    return value is LocalValue local && seen.Add(local.Variable) && definitions.TryGetValue(local.Variable, out var sources)
                        && sources.All(v => Origin(v, terminal, new(seen)));
                }
                bool Receiver(ManagedValue value) => Origin(value, v => v.Equals(list), []);
                bool Field(ManagedValue value, string name) => Origin(value, v => v is FieldValue f && f.Field.DeclaringType.Equals(owner)
                    && f.Field.Field.Name == name && Receiver(f.Receiver), []);
                bool Array(ManagedValue value) => Field(value, "_items");
                bool Capacity(ManagedValue value) => Origin(value, v => v is ArrayLengthValue length && Array(length.Array), []);
                bool Increment(ManagedValue value, string name) => Origin(value, v => v is BinaryValue { Op: BinOp.Add, Right: ConstantValue { Bits: 1 } } add && Field(add.Left, name), []);
                bool Scalar(ManagedValue value) => Origin(value, v => v is ConstantValue || Field(v, "_version") || Field(v, "_size") || Capacity(v)
                    || v is BinaryValue { Op: BinOp.Add, Right: ConstantValue { Bits: 1 } } add && (Field(add.Left, "_size") || Field(add.Left, "_version")), []);
                var region = new HashSet<ulong>();
                var locals = new HashSet<Variable>();
                (ulong Block, int Index)? end = null;
                var budget = 512;
                (List<ManagedValue> Items, int Versions, int Sizes, int Fast)? Visit(ulong address, int index, HashSet<ulong> path)
                {
                    if (--budget < 0 || !path.Add(address) || !blocks.TryGetValue(address, out var block)) return null;
                    region.Add(address);
                    var items = new List<ManagedValue>();
                    var versions = 0;
                    var sizes = 0;
                    var fast = 0;
                    for (var i = index; i < block.Statements.Count; i++)
                    {
                        var statement = block.Statements[i];
                        switch (statement)
                        {
                            case ManagedAssignment a when Array(a.Value) || Scalar(a.Value): locals.Add(a.Target.Variable); break;
                            case ManagedStore s when Field(s.Target, "_version") && Increment(s.Value, "_version"): versions++; break;
                            case ManagedStore s when Field(s.Target, "_size") && Increment(s.Value, "_size"): sizes++; break;
                            case ManagedStore { Target: ArrayElementValue element, Value: ConstantValue or StringValue } s
                                when Array(element.Array) && Field(element.Index, "_size"):
                                items.Add(s.Value); fast++; break;
                            case ManagedCall { Tail: false, Result: null, Invocation: { Method.Method.Name: "AddWithResize", Receiver: { } receiver, Arguments: [ConstantValue or StringValue] } invocation }
                                when invocation.Method.DeclaringType.Equals(owner) && Receiver(receiver):
                                items.Add(invocation.Arguments[0]); break;
                            case ManagedCheck { Exception.Method.Owner.FullName: "System.NullReferenceException", Condition: ComparisonValue { Condition: Cond.Eq, Right: ConstantValue { Bits: 0 } } test }
                                when Array(test.Left):
                                break;
                            case ManagedStore s when s.Target is FieldValue or StaticFieldValue && Receiver(s.Value):
                                if (end is { } previous && previous != (address, i)) return null;
                                end = (address, i);
                                return (items, versions, sizes, fast);
                            case ManagedJump jump:
                                {
                                    if (jump.Edge.Copies.Any(c => !Array(c.Value))) return null;
                                    foreach (var copy in jump.Edge.Copies) locals.Add(copy.Target.Variable);
                                    if (Visit(jump.Edge.Target, 0, new(path)) is not { } tail) return null;
                                    items.AddRange(tail.Items);
                                    return (items, versions + tail.Versions, sizes + tail.Sizes, fast + tail.Fast);
                                }
                            case ManagedBranch branch when branch.Condition is ComparisonValue { Condition: Cond.Ult or Cond.Uge } test
                                && Field(test.Left, "_size") && Capacity(test.Right):
                                {
                                    if (branch.Taken.Copies.Count != 0 || branch.Fallthrough.Copies.Count != 0
                                        || Visit(branch.Taken.Target, 0, new(path)) is not { } a
                                        || Visit(branch.Fallthrough.Target, 0, new(path)) is not { } b
                                        || !a.Items.SequenceEqual(b.Items) || a.Versions != b.Versions
                                        || a.Sizes != a.Fast || b.Sizes != b.Fast) return null;
                                    items.AddRange(a.Items);
                                    return (items, versions + a.Versions, sizes + a.Sizes, fast + a.Fast);
                                }
                            default: return null;
                        }
                    }
                    return null;
                }
                if (Visit(startBlock.Address, start + 1, []) is not { } result || end is not { } finish || result.Items.Count == 0
                    || result.Versions != result.Items.Count || result.Sizes != result.Fast) continue;
                var finalBlock = blocks[finish.Block];
                var removed = region.SelectMany(address => blocks[address].Statements
                    .Skip(address == startBlock.Address ? start + 1 : 0)
                    .Take(address == finish.Block ? finish.Index - (address == startBlock.Address ? start + 1 : 0) : int.MaxValue))
                    .ToHashSet(ReferenceEqualityComparer.Instance);
                if (body.Blocks.Where(b => !region.Contains(b.Address)).SelectMany(b => b.Statements).SelectMany(ManagedValues.Edges)
                        .Any(e => region.Contains(e.Target) && e.Target != startBlock.Address)
                    || body.Blocks.SelectMany(b => b.Statements).Where(s => !removed.Contains(s))
                        .SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))).SelectMany(ManagedValues.Walk)
                        .OfType<LocalValue>().Any(l => locals.Contains(l.Variable))) continue;
                var add = owner.Definition.Methods.SingleOrDefault(m => m.Name == "Add" && !m.IsStatic && m.Parameters.Count == 1);
                if (add is null) continue;
                var method = new MethodRef(add, owner.Arguments, []);
                var statements = startBlock.Statements.Take(start + 1).Concat(result.Items.Select(item =>
                    (ManagedStatement)new ManagedCall(allocation.Address, new(method, list, [item], true), null, false)))
                    .Concat(finalBlock.Statements.Skip(finish.Index)).ToArray();
                matched(allocation.Address, method);
                return body with
                {
                    Blocks = body.Blocks.Where(b => !region.Contains(b.Address) || b.Address == startBlock.Address)
                    .Select(b => b.Address == startBlock.Address ? b with { Statements = statements } : b).ToArray()
                };
            }
        return null;
    }
}
