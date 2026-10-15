using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>按已知字段布局拆分和组装寄存器中的值类型。数字保持位型，引用只允许完整且类型相容的传递。</summary>
public sealed class AggregateValues(ManagedTypes types)
{
    private sealed record Leaf(int Offset, TypeRef Type, IReadOnlyList<FieldRef> Path);
    private readonly Dictionary<TypeRef, IReadOnlyList<Leaf>?> layouts = new();

    /// <summary>将完整、无填充的数值字段按原始位型拼成机器整数；不将引用或未知区域解释成位。</summary>
    public ManagedValue? Bits(ManagedValue value)
    {
        if (types.Kind(value.Type) != ValueKind.Struct || types.Size(value.Type) * 8 != value.Width || Integer(value.Width) is not { } integer
            || types.FieldSpan(value.Type, 0, value.Width / 8) is not { Count: > 0 } fields) return null;
        var pieces = fields.Select(field => (field.Offset, Value: Field(value, new Leaf(field.Offset, field.Type, field.Path)))).ToArray();
        return Range(pieces, 0, value.Width) is { } bits && Numeric(bits.Type) ? As(bits, integer) : null;
    }

    public ManagedValue? Project(ManagedValue value, int offset, int width)
    {
        if (offset < 0 || width <= 0 || width % 8 != 0 || offset * 8 + width > value.Width) return null;
        if (offset == 0 && width == value.Width) return value;
        if (types.Kind(value.Type) != ValueKind.Struct) return Slice(value, offset * 8, width);
        if (types.FieldPath(value.Type, offset, width / 8) is { } path)
        {
            foreach (var field in path) value = new FieldValue(value, field.Field, field.Type, types.Size(field.Type) * 8);
            return value;
        }
        if (Layout(value.Type) is not { } leaves) return null;
        var pieces = leaves.Select(leaf => (leaf.Offset, Value: Field(value, leaf))).ToArray();
        return Range(pieces, offset, width);
    }

    public ManagedValue? Assemble(TypeRef type, IReadOnlyList<(int Offset, ManagedValue Value)> pieces)
    {
        var size = types.Size(type);
        if (types.Kind(type) != ValueKind.Struct || size <= 0 || pieces.Count == 0) return null;
        var ordered = pieces.OrderBy(p => p.Offset).ToArray();
        var end = 0;
        foreach (var (offset, value) in ordered)
        {
            if (offset < end || value.Width <= 0 || value.Width % 8 != 0 || offset + value.Width / 8 > size) return null;
            end = offset + value.Width / 8;
        }
        if (ordered is [(0, var whole)] && whole.Type == type && whole.Width == size * 8) return whole;
        if (Layout(type) is not { Count: > 0 } leaves) return null;
        var members = new List<AggregateMember>();
        foreach (var leaf in leaves)
        {
            if (Range(ordered, leaf.Offset, types.Size(leaf.Type) * 8) is not { } value || As(value, leaf.Type) is not { } typed) return null;
            members.Add(new(leaf.Path, typed));
        }
        return ordered.All(p => p.Value is ConstantValue { Bits: 0 })
            ? new DefaultValue(type, size * 8) : new AggregateValue(type, size * 8, members);
    }

    private ManagedValue? As(ManagedValue value, TypeRef type)
    {
        if (value.Type == type || types.IsAssignable(value.Type, type)) return value;
        if (Numeric(value.Type) && Numeric(type) && types.Size(type) * 8 == value.Width)
            return new ConversionValue(ConvKind.Bitcast, value, type, value.Width);
        return ManagedTypes.IsReferenceType(type) && value is ConstantValue { Bits: 0 } ? new ConstantValue(0, type, 64) : null;
    }

    private ManagedValue Field(ManagedValue value, Leaf leaf)
    {
        foreach (var field in leaf.Path)
        {
            var type = field.Field.Type.Substitute(field.DeclaringType is DefinitionRef d ? d.Arguments : [], []);
            value = new FieldValue(value, field, type, types.Size(type) * 8);
        }
        return value;
    }

    private ManagedValue? Range(IReadOnlyList<(int Offset, ManagedValue Value)> pieces, int offset, int width)
    {
        var end = offset + width / 8;
        var next = offset;
        var parts = new List<(int Shift, ManagedValue Value)>();
        foreach (var (start, value) in pieces.OrderBy(p => p.Offset))
        {
            var stop = start + value.Width / 8;
            if (stop <= offset || start >= end) continue;
            var first = Math.Max(offset, start);
            var last = Math.Min(end, stop);
            if (first != next || Project(value, first - start, (last - first) * 8) is not { } part) return null;
            parts.Add(((first - offset) * 8, part));
            next = last;
        }
        if (next != end || parts.Count == 0) return null;
        if (parts.Count == 1) return parts[0].Value;
        if (Integer(width) is not { } integer || parts.Any(p => !Numeric(p.Value.Type))) return null;
        ManagedValue? combined = null;
        foreach (var (shift, part) in parts)
        {
            ManagedValue bits = new ConversionValue(ConvKind.ZeroExtend, part, integer, width);
            if (shift > 0) bits = new BinaryValue(BinOp.Shl, bits, new ConstantValue((ulong)shift, integer, width), integer, width);
            combined = combined is null ? bits : new BinaryValue(BinOp.Or, combined, bits, integer, width);
        }
        return combined;
    }

    private ManagedValue? Slice(ManagedValue value, int shift, int width)
    {
        if (!Numeric(value.Type) || Integer(value.Width) is not { } sourceType || Integer(width) is not { } resultType) return null;
        ManagedValue bits = new ConversionValue(ConvKind.Bitcast, value, sourceType, value.Width);
        if (shift > 0) bits = new BinaryValue(BinOp.LShr, bits, new ConstantValue((ulong)shift, sourceType, value.Width), sourceType, value.Width);
        return width == value.Width ? bits : new ConversionValue(ConvKind.Truncate, bits, resultType, width);
    }

    private TypeRef? Integer(int width) => width is 8 or 16 or 32 or 64 ? types.Integer(width, false) : null;
    private bool Numeric(TypeRef type) => types.Kind(type) is ValueKind.Int or ValueKind.Bool or ValueKind.Float or ValueKind.Double;

    private IReadOnlyList<Leaf>? Layout(TypeRef type)
    {
        if (layouts.TryGetValue(type, out var cached)) return cached;
        var leaves = new List<Leaf>();
        bool Visit(TypeRef current, int offset, IReadOnlyList<FieldRef> path, HashSet<TypeRef> active)
        {
            if (types.Kind(current) != ValueKind.Struct)
            {
                if (types.Size(current) <= 0) return false;
                leaves.Add(new(offset, current, path));
                return true;
            }
            if (!active.Add(current) || types.Fields(current) is not { } fields) return false;
            var end = 0;
            foreach (var field in fields)
            {
                var size = types.Size(field.Type);
                if (size <= 0 || field.Offset < end || field.Offset + size > types.Size(current)) return false;
                if (!Visit(field.Type, offset + field.Offset, [.. path, field.Field], active)) return false;
                end = field.Offset + size;
            }
            active.Remove(current);
            return true;
        }
        var result = Visit(type, 0, [], []) ? leaves : null;
        layouts.Add(type, result);
        return result;
    }
}
