using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery;

/// <summary>按直接基类的完整直线方法体认回被内联的构造调用，保留本类字段初始化的顺序。</summary>
public static class BaseConstructorCalls
{
    public static ManagedBody Rewrite(ManagedBody body, IReadOnlyList<ManagedBody> candidates)
    {
        if (body.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }) return body;
        var parent = body.Method.Method.Owner.BaseType?.Substitute(body.Method.TypeArguments, []);
        if (body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Invocation.Method.Method.Name == ".ctor"
            && c.Invocation.Receiver is ArgumentValue { Index: -1 }
            && (c.Invocation.Method.DeclaringType.Equals(parent) || c.Invocation.Method.DeclaringType.Equals(body.Method.DeclaringType)))) return body;
        var constructors = candidates.Where(c => c.Method.Method is { Name: ".ctor", IsStatic: false } && c.Method.DeclaringType.Equals(parent)).ToArray();
        // 无参基类构造若只转调自己的直接基类，可原位替换该调用，不要求派生构造的其他部分符合直线模板。
        foreach (var candidate in constructors.Where(c => c.Method.Method.Parameters.Count == 0))
        {
            if (Effects(candidate) is not [ManagedCall { Invocation: { Method.Method.Name: ".ctor", Receiver: ArgumentValue { Index: -1 },
                    Arguments.Count: 0, Virtual: false } } forwarded]
                || !forwarded.Invocation.Method.DeclaringType.Equals(candidate.Method.Method.Owner.BaseType?.Substitute(candidate.Method.TypeArguments, []))) continue;
            bool Matches(ManagedStatement statement) => statement is ManagedCall { Invocation: { Receiver: ArgumentValue { Index: -1 },
                Arguments.Count: 0, Virtual: false } } call && call.Invocation.Method.Equals(forwarded.Invocation.Method);
            if (!body.Blocks.SelectMany(b => b.Statements).Any(Matches)) continue;
            return body with { Blocks = body.Blocks.Select(block => block with
            {
                Statements = block.Statements.SelectMany(statement =>
                {
                    if (!Matches(statement)) return new[] { statement };
                    var call = (ManagedCall)statement;
                    var restored = call with { Invocation = call.Invocation with { Method = candidate.Method }, Tail = false, Inlined = true };
                    return call.Tail ? new ManagedStatement[] { restored, new ManagedReturn(call.Address, null) } : [restored];
                }).ToArray(),
            }).ToArray() };
        }
        if (Effects(body, keepComputations: true) is not { } statements) return body;
        foreach (var candidate in constructors)
        {
            if (Effects(candidate) is not { Count: > 0 } pattern) continue;
            for (var start = 0; start + pattern.Count <= statements.Count; start++)
            {
                var arguments = new Dictionary<int, ManagedValue>();
                bool Value(ManagedValue expected, ManagedValue actual)
                {
                    if (expected is ArgumentValue argument)
                    {
                        if (arguments.TryGetValue(argument.Index, out var bound)) return bound.Equals(actual);
                        if (argument.Index == -1 ? actual is not ArgumentValue { Index: -1 }
                            : !Pure(actual) || !argument.Type.Equals(actual.Type)) return false;
                        arguments[argument.Index] = actual;
                        return true;
                    }
                    var left = ManagedValues.Children(expected).ToArray();
                    var right = ManagedValues.Children(actual).ToArray();
                    if (left.Length != right.Length || !left.Zip(right).All(p => Value(p.First, p.Second))) return false;
                    var index = 0;
                    return ManagedValues.Map(expected, _ => right[index++]).Equals(actual);
                }
                bool Statement(ManagedStatement expected, ManagedStatement actual) => (expected, actual) switch
                {
                    (ManagedStore a, ManagedStore b) => Value(a.Target, b.Target) && Value(a.Value, b.Value),
                    (ManagedCall a, ManagedCall b) => a.Invocation.Method.Equals(b.Invocation.Method)
                        && a.Invocation.Virtual == b.Invocation.Virtual && a.Invocation.Arguments.Count == b.Invocation.Arguments.Count
                        && (a.Invocation.Receiver is { } receiver ? b.Invocation.Receiver is { } other && Value(receiver, other) : b.Invocation.Receiver is null)
                        && a.Invocation.Arguments.Zip(b.Invocation.Arguments).All(p => Value(p.First, p.Second)),
                    _ => false,
                };
                if (!pattern.Select((s, i) => Statement(s, statements[start + i])).All(x => x)
                    || !arguments.TryGetValue(-1, out var self)
                    || Enumerable.Range(0, candidate.Method.Method.Parameters.Count).Any(i => !arguments.ContainsKey(i))) continue;
                var call = new ManagedCall(statements[start].Address,
                    new(candidate.Method, self, Enumerable.Range(0, candidate.Method.Method.Parameters.Count).Select(i => arguments[i]).ToArray(), false), null, false) { Inlined = true };
                return body with { Blocks = [new(body.Blocks[0].Address,
                    [.. statements.Take(start), call, .. statements.Skip(start + pattern.Count), new ManagedReturn(body.Blocks[^1].Statements[^1].Address, null)])] };
            }
        }
        return body;
    }

    private static bool Pure(ManagedValue value) => value is ArgumentValue or ConstantValue or StringValue
        || value is ConversionValue conversion && Pure(conversion.Operand);

    private static List<ManagedStatement>? Effects(ManagedBody body, bool keepComputations = false)
    {
        if (body.Regions.Count != 0 || body.Blocks.Count == 0) return null;
        if (body.Blocks.SelectMany(b => b.Statements).SelectMany(ManagedValues.Of).SelectMany(ManagedValues.Walk)
            .Any(v => v is AddressValue { Target: LocalValue })) return null;
        var blocks = body.Blocks.ToDictionary(b => b.Address);
        var seen = new HashSet<ulong>();
        var locals = new Dictionary<LocalValue, ManagedValue>();
        ManagedValue Resolve(ManagedValue value) => value is LocalValue local && locals.TryGetValue(local, out var source)
            ? source : ManagedValues.Map(value, Resolve);
        var effects = new List<ManagedStatement>();
        var block = body.Blocks[0];
        while (seen.Add(block.Address))
        {
            foreach (var statement in block.Statements)
            {
                var mapped = ManagedValues.Map(statement, Resolve);
                switch (mapped)
                {
                    case ManagedAssignment assignment when Pure(assignment.Value):
                        locals[assignment.Target] = assignment.Value;
                        break;
                    case ManagedAssignment assignment when keepComputations:
                        locals.Remove(assignment.Target);
                        effects.Add(assignment);
                        break;
                    case ManagedStore store: effects.Add(store); break;
                    case ManagedCall { Result: { } result, Tail: false } call when keepComputations:
                        locals.Remove(result);
                        effects.Add(call);
                        break;
                    case ManagedCall { Result: null } call:
                        effects.Add(call with { Tail = false });
                        if (call.Tail) return seen.Count == blocks.Count ? effects : null;
                        break;
                    case ManagedReturn { Value: null }: return seen.Count == blocks.Count ? effects : null;
                    case ManagedJump { Edge.Copies.Count: 0 }: break;
                    default: return null;
                }
            }
            if (block.Statements[^1] is not ManagedJump jump || !blocks.TryGetValue(jump.Edge.Target, out block!)) return null;
        }
        return null;
    }
}

public sealed partial class MethodRecovery
{
    private readonly Dictionary<MethodRef, ManagedBody?> baseConstructorBodies = new();

    private ManagedBody RestoreBaseConstructor(ManagedBody body)
    {
        if (body.Method.Method is not { Name: ".ctor", IsStatic: false, Owner.IsValueType: false }
            || body.Method.Method.Owner.BaseType?.Substitute(body.Method.TypeArguments, []) is not DefinitionRef parent
            || body.Blocks.SelectMany(b => b.Statements).OfType<ManagedCall>().Any(c => c.Invocation.Method.Method.Name == ".ctor"
                && c.Invocation.Receiver is ArgumentValue { Index: -1 } && c.Invocation.Method.DeclaringType.Equals(parent))) return body;
        var candidates = new List<ManagedBody>();
        foreach (var method in parent.Definition.Methods.Where(m => m is { Name: ".ctor", IsStatic: false }))
        {
            var reference = new MethodRef(method, parent.Arguments, []);
            if (!baseConstructorBodies.TryGetValue(reference, out var candidate))
            {
                var entry = ConstructorEntry(reference);
                candidate = entry != 0 && facts.Code.RegionOf(entry) == CodeRegion.Managed
                    ? RecoverInstance(reference, entry).Body : null;
                baseConstructorBodies[reference] = candidate;
            }
            if (candidate is not null) candidates.Add(candidate);
        }
        return BaseConstructorCalls.Rewrite(body, candidates);
    }
}
