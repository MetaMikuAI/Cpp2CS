namespace Cpp2CS.Recovery.Inlining;

/// <summary>已证明的值类型构造；实参的 IL 类型转换由下降完成。</summary>
internal sealed record ValueConstruction(MethodRef Constructor, IReadOnlyList<ManagedValue> Arguments);

internal sealed partial class TemplateRecovery
{
    private sealed record ValueConstructorEvidence(MethodRef Method, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> Writes);
    private readonly Dictionary<DefinitionRef, ValueConstructorEvidence[]> valueConstructors = [];

    /// <summary>构造体纯粹写入全部叶子，且写入值为形参、经 ref 形参的读取或常量。</summary>
    private ValueConstructorEvidence[] ValueConstructors(DefinitionRef structure)
    {
        if (valueConstructors.TryGetValue(structure, out var known)) return known;
        var candidates = new List<ValueConstructorEvidence>();
        foreach (var definition in structure.Definition.Methods.Where(m => m.Name == ".ctor" && !m.IsStatic && m.GenericParameters.Count == 0))
        {
            var method = new MethodRef(definition, structure.Arguments, []);
            if (ConstructorWrites(method) is not { Count: > 0 } writes) continue;
            if (writes.All(w => w.Value is ConstantValue or ArgumentValue { Index: >= 0 }
                    or IndirectValue { Address: ArgumentValue { Index: >= 0, Type: ByRefRef } })
                && types.Leaves(structure).All(l => writes.Any(w => FieldPrefix(w.Path, l.Path))))
                candidates.Add(new(method, writes));
        }
        return valueConstructors[structure] = candidates.ToArray();
    }

    public bool CanConstructValue(DefinitionRef structure) => ValueConstructors(structure).Length > 0;

    /// <summary>
    /// 以构造函数自身的恢复体证明给定叶子值：最终写入覆盖全部叶子，每个形参均绑定且各次出现一致。
    /// 新值在构造完成前不可见，因此只比较最终写入；不能证明时保留调用方的缺口。
    /// </summary>
    public ValueConstruction? ProveValueConstruction(DefinitionRef structure, IReadOnlyList<(IReadOnlyList<FieldRef> Path, ManagedValue Value)> leaves)
    {
        foreach (var candidate in ValueConstructors(structure))
        {
            var (method, writes) = candidate;
            var binding = new Dictionary<int, ManagedValue>();
            var valid = true;
            foreach (var (path, written) in writes)
            {
                var desired = leaves.FirstOrDefault(f => f.Path.SequenceEqual(path)).Value;
                if (desired is null)
                {
                    if (leaves.Any(f => FieldPrefix(path, f.Path))) { valid = false; break; }
                    var field = path[^1];
                    var type = field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
                    desired = types.Kind(type) == TypeKind.Struct ? new ComposedValue(type, []) : new ConstantValue(0, type, Width(type));
                }
                valid = written switch
                {
                    ConstantValue constant => desired.Equals(constant),
                    IndirectValue { Address: ArgumentValue { Index: >= 0, Type: ByRefRef reference } argument } => desired.Type.Equals(reference.Element)
                        && desired is LocalValue or ArgumentValue or FieldValue or StaticFieldValue or ArrayElementValue
                        && Unify(argument, new AddressValue(desired), binding),
                    ArgumentValue { Index: >= 0 } => Unify(written, desired, binding),
                    _ => false,
                };
                if (!valid) break;
            }
            if (!valid || Enumerable.Range(0, method.Method.Parameters.Count).Any(i => !binding.ContainsKey(i))
                || !leaves.All(f => writes.Any(w => FieldPrefix(w.Path, f.Path)))) continue;
            return new(method, Enumerable.Range(0, method.Method.Parameters.Count).Select(i => binding[i]).ToArray());
        }
        return null;
    }

    private static bool FieldPrefix(IReadOnlyList<FieldRef> prefix, IReadOnlyList<FieldRef> path) =>
        path.Count >= prefix.Count && path.Take(prefix.Count).SequenceEqual(prefix);
}
