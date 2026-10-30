using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>单字段结构体仅经标量局部和分支复制后重组时，保留原结构体值。</summary>
internal static class SourceScalarStructCopies
{
    public static ManagedBody Rewrite(ManagedBody body)
    {
        var candidates = body.Blocks.SelectMany(b => b.Statements).SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<ComposedValue>().Where(c => c.StructType is DefinitionRef
            { Definition: { IsValueType: true, IsEnum: false, Keyword: null } } type
                && (type.Definition.Attributes & System.Reflection.TypeAttributes.LayoutMask) != System.Reflection.TypeAttributes.ExplicitLayout
                && type.Definition.Fields.Count(f => !f.IsStatic) == 1 && c.Leaves is [{ Path.Count: 1, Value: LocalValue }])
            .ToArray();
        foreach (var candidate in candidates)
        {
            var field = candidate.Leaves[0].Path[0];
            var type = candidate.StructType;
            if (!field.DeclaringType.Equals(type)) continue;
            var seed = (LocalValue)candidate.Leaves[0].Value;
            var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
            var copies = statements.OfType<ManagedAssignment>().Select(a => new ManagedCopy(a.Target, a.Value))
                .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies)).ToArray();
            var writes = copies.GroupBy(c => c.Target.Variable).ToDictionary(g => g.Key, g => g.ToArray());
            var connected = new HashSet<Variable>();
            var pending = new Stack<Variable>([seed.Variable]);
            var valid = true;
            while (pending.TryPop(out var variable))
            {
                if (!connected.Add(variable)) continue;
                if (!writes.TryGetValue(variable, out var incoming) || incoming.Any(c => !c.Target.Type.Equals(seed.Type)))
                { valid = false; break; }
                foreach (var copy in incoming)
                    if (copy.Value is LocalValue local) pending.Push(local.Variable);
                foreach (var copy in copies)
                    if (copy.Value is LocalValue local && local.Variable == variable) pending.Push(copy.Target.Variable);
            }
            if (!valid) continue;
            ManagedValue? Root(ManagedValue value) => value is FieldValue { Accessor: null } member && member.Field.Equals(field)
                && (member.Receiver is AddressValue address ? address.Target : member.Receiver) is var root && root.Type.Equals(type) ? root : null;
            bool Rebuilt(ManagedValue value) => value is ComposedValue composed && composed.Type.Equals(type)
                && composed.Leaves is [{ Path.Count: 1, Value: LocalValue local }]
                && composed.Leaves[0].Path[0].Equals(field) && connected.Contains(local.Variable);
            bool Allowed(ManagedValue value)
            {
                if (Rebuilt(value)) return true;
                if (value is LocalValue local && connected.Contains(local.Variable)) return false;
                return ManagedValues.Children(value).All(Allowed);
            }
            bool Incoming(ManagedValue value) => value is LocalValue local && connected.Contains(local.Variable)
                || value is ConstantValue { Bits: 0 } || Root(value) is { } root && Allowed(root);
            if (copies.Any(c => connected.Contains(c.Target.Variable) ? !Incoming(c.Value) : !Allowed(c.Value))
                || statements.Any(s => (s is ManagedAssignment a
                    ? connected.Contains(a.Target.Variable) ? [] : new[] { a.Value }
                    : ManagedValues.Of(s)).Any(v => !Allowed(v)))
                || statements.OfType<ManagedCall>().Any(c => c.Result is { } r && connected.Contains(r.Variable))
                || statements.OfType<ManagedAwait>().Any(c => c.Result is { } r && connected.Contains(r.Variable))) continue;
            LocalValue Local(LocalValue value) => new(value.Variable, type, 0);
            ManagedValue Copy(ManagedValue value) => value is LocalValue local ? Local(local)
                : value is ConstantValue { Bits: 0 } ? new ComposedValue(type, []) : Root(value)!;
            ManagedValue Map(ManagedValue value) => Rebuilt(value) ? Local((LocalValue)((ComposedValue)value).Leaves[0].Value)
                : ManagedValues.Map(value, Map);
            body = body with
            {
                Blocks = body.Blocks.Select(b => b with
                {
                    Statements = b.Statements.Select(s =>
            {
                var mapped = s is ManagedAssignment a && connected.Contains(a.Target.Variable)
                    ? a with { Target = Local(a.Target), Value = Copy(a.Value) } : ManagedValues.Map(s, Map);
                return ManagedValues.MapEdges(mapped, edge => edge with
                {
                    Copies = edge.Copies.Select(c => connected.Contains(c.Target.Variable)
                    ? new ManagedCopy(Local(c.Target), Copy(c.Value)) : c).ToArray()
                });
            }).ToArray()
                }).ToArray()
            };
        }
        return body;
    }
}
