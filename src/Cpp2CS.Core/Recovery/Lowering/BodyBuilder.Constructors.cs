using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>以构造函数自身的字段写入为证据，将完整字段值还原为构造调用。</summary>
    private ManagedValue? ValueConstructor(DefinitionRef structure, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> fields)
    {
        bool Prefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) => path.Take(prefix.Count).SequenceEqual(prefix);
        foreach (var definition in structure.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.GenericParameters.Count == 0))
        {
            var method = new MethodRef(definition, structure.Arguments, []);
            if (summaries(method) is not { Body: { Regions.Count: 0 } body }) continue;
            var statements = body.Blocks.SelectMany(b => b.Statements).Where(s => s is not ManagedJump).ToArray();
            if (statements.LastOrDefault() is not ManagedReturn { Value: null }
                || statements.Any(s => s is not (ManagedStore or ManagedReturn or ManagedAssignment { Value: ArgumentValue or ConstantValue or LocalValue }))) continue;
            var assignments = statements.OfType<ManagedAssignment>().GroupBy(a => a.Target.Variable).ToArray();
            if (assignments.Any(g => g.Count() != 1)) continue;
            var aliases = assignments.ToDictionary(g => g.Key, g => g.Single().Value);
            ManagedValue Through(ManagedValue value) => value is LocalValue local && aliases.TryGetValue(local.Variable, out var held) ? Through(held) : value;
            var arguments = new ManagedValue?[definition.Parameters.Count];
            var written = new List<IReadOnlyList<FieldRef>>();
            var valid = true;
            IEnumerable<ManagedStore> Writes(ManagedStore store)
            {
                if (store is not { Target: IndirectValue { Address: ArgumentValue { Index: -1 } self }, Value: ComposedValue composed })
                { yield return store; yield break; }
                foreach (var (path, type, _) in Leaves(structure, 0))
                {
                    ManagedValue target = self;
                    foreach (var field in path) target = new FieldValue(target, field, FieldType(field, null), Width(FieldType(field, null)));
                    var value = composed.Leaves.FirstOrDefault(l => l.Path.SequenceEqual(path)).Value ?? new ConstantValue(0, type, Width(type));
                    yield return new ManagedStore(store.Address, target, value);
                }
            }
            foreach (var store in statements.OfType<ManagedStore>().SelectMany(Writes))
            {
                var path = new List<FieldRef>();
                var target = store.Target;
                while (target is FieldValue or AddressValue)
                    if (target is FieldValue field) { path.Insert(0, field.Field); target = Through(field.Receiver); }
                    else target = Through(((AddressValue)target).Target);
                if (target is not ArgumentValue { Index: -1 } || path.Count == 0
                    || written.Any(p => Prefix(p, path) || Prefix(path, p))) { valid = false; break; }
                written.Add(path);
                var desired = fields.FirstOrDefault(f => f.Path.SequenceEqual(path)).Value;
                if (desired is null)
                {
                    if (fields.Any(f => Prefix(path, f.Path))) { valid = false; break; }
                    var type = FieldType(path[^1], null);
                    desired = types.Kind(type) == TypeKind.Struct ? new ComposedValue(type, []) : new ConstantValue(0, type, Width(type));
                }
                switch (Through(store.Value))
                {
                    case ArgumentValue { Index: >= 0 } argument when argument.Index < arguments.Length:
                        var value = Coerce(desired, TypeOracle.Concrete(method, definition.Parameters[argument.Index].Type));
                        if (arguments[argument.Index] is { } bound && !bound.Equals(value)) valid = false;
                        arguments[argument.Index] = value;
                        break;
                    case ConstantValue constant when Coerce(desired, constant.Type).Equals(constant):
                        break;
                    default:
                        valid = false;
                        break;
                }
                if (!valid) break;
            }
            if (valid && arguments.All(a => a is not null) && fields.All(f => written.Any(p => Prefix(p, f.Path)))
                && Leaves(structure, 0).All(f => written.Any(p => Prefix(p, f.Path))))
                return new NewObjectValue(method, arguments.Select(a => a!).ToArray()) { Transparent = true };
        }
        return null;
    }
}
