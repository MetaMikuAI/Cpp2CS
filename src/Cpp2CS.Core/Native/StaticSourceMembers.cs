namespace Cpp2CS.Native;

// 从静态存储布局找回字段；属性必须由独立机器 getter 的完整返回体证明。
public sealed class StaticSourceMembers(HeaderLayout layouts, ManagedNames managed, Symbols symbols, Func<ulong, LiftResult> lift)
{
    private readonly Dictionary<StaticMemberExpression, Expression> properties = [];
    private readonly Dictionary<StaticMemberExpression, Proof> proofs = [];
    private static Expression Expand(Expression e) => e is CapturedExpression c ? Expand(c.Value) : e;
    private StaticMemberExpression? Field(Expression e)
    {
        MemberExpression[] parts; int size;
        if (e is AggregateExpression { Bits: ComposeExpression compose } && compose.Parts.All(p => p is MemberExpression))
        { parts = compose.Parts.Cast<MemberExpression>().ToArray(); size = compose.BitWidths.Sum() / 8;
            if (!parts.Select(p => p.Field.Size * 8).SequenceEqual(compose.BitWidths)) return null; }
        else if (e is MemberExpression member) { parts = [member]; size = member.Field.Size; }
        else return null;
        if (parts.Length == 0 || Expand(parts[0].Receiver) is not MemberExpression { Field.Name: "static_fields", Receiver: MetadataExpression { IsSlot: false, Reference.Kind: "ScriptMetadata" } metadata } storage ||
            parts.Any(p => Expand(p.Receiver) != storage) || !metadata.Reference.Name.EndsWith("_TypeInfo")) return null;
        var offset = parts[0].Field.Offset;
        foreach (var part in parts) { if (part.Field.Offset != offset) return null; offset += part.Field.Size; }
        var fields = layouts.Members(storage.Field.Type).Where(f => f.Offset == parts[0].Field.Offset && f.Size == size).ToArray();
        if (fields.Length != 1) return null;
        var owner = metadata.Reference.Name[..^9];
        var field = managed.StaticField(owner, fields[0].Name);
        if (field is null || e is AggregateExpression aggregate && field.Value.Type != aggregate.Type) return null;
        return new(owner, field.Value.Name, field.Value.Type);
    }
    public LiftResult Normalize(LiftResult source, bool getters = true)
    {
        var used = new HashSet<StaticMemberExpression>();
        var view = SourceTree.Map(source, e =>
        {
            var field = Field(e);
            if (field is null) return e;
            if (!getters) return field;
            used.Add(field);
            if (properties.TryGetValue(field, out var known)) return known;
            var candidates = new List<(string Name, ulong Address)>();
            foreach (var getter in managed.StaticGetters(field.Owner, field.Type))
            {
                if (!symbols.NamedMethods.TryGetValue(field.Owner + "$$" + getter, out var methods) || methods.Length != 1 || symbols.Unique(methods[0].Address) is null) continue;
                var body = Normalize(ViewNormalizer.Normalize(lift(methods[0].Address)), false);
                var statements = body.Blocks.Values.SelectMany(b => b.Statements).Where(s => s is not EnsureMetadataStatement).ToArray();
                if (body.Problems.Count == 0 && body.Blocks.Count == 1 && body.Blocks.Values.Single().Successors.Length == 0 &&
                    statements is [ReturnStatement { Value: StaticMemberExpression value }] && value == field) candidates.Add((getter[4..], methods[0].Address));
            }
            Expression result = candidates.Count == 1 ? field with { Name = candidates[0].Name, IsProperty = true } : field;
            if (candidates.Count == 1) proofs[field] = new(candidates[0].Address, "SourceStaticGetter", $"{field.Owner}.{field.Name}: exact contiguous static field layout; unique public getter {candidates[0].Name}; complete native body returns only the same field after metadata initialization");
            properties[field] = result;
            return result;
        });
        foreach (var block in view.Blocks.Values)
            block.Statements.RemoveAll(s => s is AssignStatement { Value: MemberExpression { Field.Name: "static_fields", Receiver: MetadataExpression }, Name: var name } &&
                view.Blocks.Values.Sum(b => b.Statements.Sum(s => ViewNormalizer.Expressions(s).Sum(e => ViewNormalizer.Count(e, name))) + (b.Condition is null ? 0 : ViewNormalizer.Count(b.Condition, name))) == 0);
        view.Proofs.AddRange(used.Where(proofs.ContainsKey).Select(f => proofs[f]));
        return view;
    }
}
