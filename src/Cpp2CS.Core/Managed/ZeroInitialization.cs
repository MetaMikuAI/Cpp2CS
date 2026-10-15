using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>将同一稳定存储上连续、完整且不重叠的字段清零恢复为结构体 default 赋值。</summary>
public static class ZeroInitialization
{
    private sealed record Location(ManagedValue Root, int Offset, TypeRef Type);
    private sealed record Write(int Index, ManagedStore Store, Location Location);
    private sealed record Candidate(ManagedValue Target, Location Location, int Size);

    public static ManagedBody Recover(ManagedTypes types, ManagedBody body)
    {
        Location? Locate(ManagedValue value)
        {
            if (value is FieldValue field)
            {
                Location? parent;
                if (field.Receiver.Type is ByRefRef reference) parent = Stable(field.Receiver) ? new(field.Receiver, 0, reference.Element) : null;
                else if (ManagedTypes.IsReferenceType(field.Receiver.Type)) parent = Stable(field.Receiver) ? new(field.Receiver, 0, field.Receiver.Type) : null;
                else parent = Locate(field.Receiver);
                if (parent is null || types.Fields(parent.Type)?.SingleOrDefault(f => f.Field == field.Field) is not { } member
                    || member.Offset < 0 || member.Type != field.Type || types.Size(field.Type) * 8 != field.Width
                    || (long)parent.Offset + member.Offset > int.MaxValue) return null;
                return new(parent.Root, parent.Offset + member.Offset, field.Type);
            }
            if (value is IndirectValue indirect && Stable(indirect.Address) && indirect.Address.Type is ByRefRef byRef && byRef.Element == value.Type
                && types.Size(value.Type) * 8 == value.Width)
                return new(indirect.Address, 0, value.Type);
            return Stable(value) && types.Kind(value.Type) == ValueKind.Struct && types.Size(value.Type) * 8 == value.Width ? new(value, 0, value.Type) : null;
        }
        bool Writable(ManagedValue value)
        {
            for (var field = value as FieldValue; field is not null; field = field.Receiver as FieldValue)
                if ((field.Field.Field.Attributes & System.Reflection.FieldAttributes.InitOnly) != 0
                    && (body.Method.Method.Name != ".ctor" || body.Method.Method.Owner != field.Field.Field.Owner
                        || field.Receiver is not ArgumentValue { Index: -1 })) return false;
            return true;
        }
        IEnumerable<Candidate> Candidates(ManagedValue target)
        {
            for (var value = target; value is not null; value = value is FieldValue field ? field.Receiver : null)
            {
                var candidate = value.Type is ByRefRef byRef && types.Kind(byRef.Element) == ValueKind.Struct
                    ? new IndirectValue(value, byRef.Element, types.Size(byRef.Element) * 8) : value;
                if (types.Kind(candidate.Type) != ValueKind.Struct || Locate(candidate) is not { } location) continue;
                var size = types.Size(candidate.Type);
                if (size <= 0 || types.FieldSpan(candidate.Type, 0, size) is null) continue;
                if (!Writable(candidate)) continue;
                yield return new(candidate, location, size);
            }
        }
        ManagedStatement Initialization(Write first, Candidate candidate)
        {
            var target = candidate.Target;
            if (target is LocalValue or ArgumentValue) target = new IndirectValue(new AddressValue(target, new ByRefRef(target.Type)), target.Type, target.Width);
            return new ManagedStore(first.Store.Address, target, new DefaultValue(candidate.Target.Type, candidate.Size * 8));
        }
        var blocks = new List<ManagedBlock>();
        foreach (var block in body.Blocks)
        {
            var output = new List<ManagedStatement>();
            for (var index = 0; index < block.Statements.Count;)
            {
                var writes = new List<Write>();
                while (index + writes.Count < block.Statements.Count
                    && block.Statements[index + writes.Count] is ManagedStore store && Zero(store.Value)
                    && Locate(store.Target) is { } location && (writes.Count == 0 || writes[0].Location.Root == location.Root))
                    writes.Add(new(index + writes.Count, store, location));
                if (writes.Count < 2) { output.Add(block.Statements[index++]); continue; }
                var replacements = new Dictionary<int, ManagedStatement?>();
                var candidates = writes.SelectMany(w => Candidates(w.Store.Target)).DistinctBy(c => c.Target).OrderByDescending(c => c.Size);
                foreach (var candidate in candidates)
                {
                    var start = candidate.Location.Offset;
                    var end = (long)start + candidate.Size;
                    var covered = writes.Where(w => w.Location.Offset < end && (long)w.Location.Offset + w.Store.Target.Width / 8 > start).ToArray();
                    if (covered.Length < 2 || covered.Any(w => replacements.ContainsKey(w.Index))) continue;
                    var cursor = (long)start;
                    var complete = true;
                    foreach (var write in covered.OrderBy(w => w.Location.Offset))
                    {
                        if (write.Location.Offset != cursor || write.Store.Target.Width <= 0 || write.Store.Target.Width % 8 != 0)
                        { complete = false; break; }
                        cursor += write.Store.Target.Width / 8;
                    }
                    if (!complete || cursor != end) continue;
                    foreach (var write in covered) replacements.Add(write.Index, null);
                    replacements[covered[0].Index] = Initialization(covered[0], candidate);
                }
                foreach (var write in writes)
                {
                    if (!replacements.TryGetValue(write.Index, out var replacement)) output.Add(write.Store);
                    else if (replacement is not null) output.Add(replacement);
                }
                index += writes.Count;
            }
            blocks.Add(block with { Statements = output });
        }
        return body with { Blocks = blocks };
    }

    private static bool Stable(ManagedValue value) => value is ArgumentValue or LocalValue or StackLocalValue;
    private static bool Zero(ManagedValue value) => value switch
    {
        ConstantValue { Bits: 0 } or DefaultValue => true,
        ConversionValue { Kind: ConvKind.Bitcast or ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => Zero(conversion.Operand),
        _ => false,
    };
}
