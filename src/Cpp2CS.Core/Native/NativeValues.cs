using Cpp2CS.IR;

namespace Cpp2CS.Native;

// 位宽与来源随值传递；寄存器、栈和聚合字段使用同一套切片规则。
public static class NativeValues
{
    public static bool IsManagedReference(string type) => type.EndsWith("_o*") || type.EndsWith("_array*") || type == "Il2CppObject*";
    public static NativeValue? ReferenceAs(NativeValue value, string type)
    {
        if (!IsManagedReference(type) || value.Bits.Width != 64) return null;
        if (value.Bits is ConstantBits { Value.IsZero: true }) return value with { Type = type, Expression = new NameExpression("null") };
        return value.Type == type || type == "Il2CppObject*" && IsManagedReference(value.Type) ? value with { Type = type } : null;
    }
    public static NativeValue[]? JoinReferences(NativeValue[] values)
    {
        var types = values.Select(v => v.Type).Where(IsManagedReference).Distinct().ToArray();
        var type = types.Length == 1 ? types[0] : types.Contains("Il2CppObject*") ? "Il2CppObject*" : null;
        if (type is null) return null;
        var converted = values.Select(v => ReferenceAs(v, type)).ToArray();
        return converted.All(v => v is not null) ? converted.Select(v => v!).ToArray() : null;
    }
    public static (string Type, Expression Left, Expression Right)? ReferenceSelection(NativeValue left, NativeValue right)
    {
        return JoinReferences([left, right]) is { } joined ? (joined[0].Type, joined[0].Expression, joined[1].Expression) : null;
    }
    public static void StoreStack(NativeState state, RegionId region, long offset, NativeValue value, string identity)
    {
        if (value.Bits.Width % 8 != 0) throw new ArgumentException("栈存储需要完整字节");
        var end = checked(offset + value.Bits.Width / 8);
        state.Stack = state.Stack.Store(identity, new(region, offset), value.Bits);
        foreach (var old in state.StackViews.Where(p => p.Key < end && p.Key + p.Value.Bits.Width / 8 > offset).ToArray())
        {
            state.StackViews.Remove(old.Key);
            if (old.Key < offset) state.StackViews.Add(old.Key, Slice(old.Value, 0, checked((int)(offset - old.Key) * 8)));
            var oldEnd = old.Key + old.Value.Bits.Width / 8;
            if (oldEnd > end) state.StackViews.Add(end, Slice(old.Value, checked((int)(end - old.Key) * 8), checked((int)(oldEnd - end) * 8)));
        }
        state.StackViews[offset] = value;
    }
    public static NativeValue Slice(NativeValue value, int offset, int width, string? type = null)
    {
        var bits = BitOps.Slice(value.Bits, offset, width);
        if (IsManagedReference(value.Type) && (offset != 0 || width != 64)) type = "native-bits";
        if (offset == 0 && width == value.Bits.Width) return value with { Type = type ?? value.Type };
        if (IntegerProjection.Width(value.Type) > 0 && (type is null || type == value.Type) && bits is ConstantBits integerBits && width <= 64)
        {
            var resultType = width is 8 or 16 or 32 or 64 ? (value.Type.StartsWith("uint") ? "uint" : "int") + width + "_t" : width <= 32 ? "uint32_t" : "uint64_t";
            var number = unchecked((long)(ulong)integerBits.Value);
            if (resultType.StartsWith("int") && width < 64 && (number & (1L << (width - 1))) != 0) number -= 1L << width;
            return new(bits, resultType, new ConstantExpression(number));
        }
        if (value.Expression is ConstantExpression && bits is ConstantBits constant && constant.Value <= long.MaxValue)
        {
            var number = (long)constant.Value;
            if (value.Type is "int8_t" or "int16_t" or "int32_t" && width <= 32 && (number & (1L << (width - 1))) != 0)
                number -= 1L << width;
            return new(bits, type ?? value.Type, new ConstantExpression(number));
        }
        if (offset == 0 && width is 8 or 16 or 32 && IntegerProjection.Width(value.Type) > width &&
            (type is null || type == value.Type) && IntegerProjection.Bits(value) is { } integer)
        {
            var narrowed = (value.Type.StartsWith("uint") ? "uint" : "int") + width + "_t";
            return new(bits, narrowed, new OperationExpression(ValueOperation.IntegerCast, narrowed, [integer]));
        }
        var naturalWidth = value.Type switch { "bool" or "uint8_t" or "int8_t" => 8,
            "uint16_t" or "int16_t" => 16, "uint32_t" or "int32_t" or "float" => 32, "double" => 64, _ => 0 };
        if (offset == 0 && width == naturalWidth && value.Expression is not SliceExpression) return new(bits, type ?? value.Type, value.Expression);
        if (offset == 0 && naturalWidth > 0 && width > naturalWidth &&
            BitOps.Slice(value.Bits, naturalWidth, width - naturalWidth) is ConstantBits { Value.IsZero: true })
            return new(bits, type ?? value.Type, value.Expression);
        if ((type is null || type == value.Type) && IntegerProjection.Extract(value, offset, width) is { } extracted) return extracted;
        var expression = value.Expression is SliceExpression slice ?
            new SliceExpression(slice.Value, checked(slice.BitOffset + offset), width) : new SliceExpression(value.Expression, offset, width);
        return new(bits, type ?? "native-bits", expression);
    }
    public static NativeValue Compose(NativeValue[] values, string type)
    {
        if (values.Length == 1) return values[0] with { Type = type };
        var bits = BitOps.Concat(values.Select(v => v.Bits));
        if (values.All(v => v.Expression is SliceExpression))
        {
            var slices = values.Select(v => (SliceExpression)v.Expression).ToArray();
            var position = slices[0].BitOffset;
            if (slices.All(s => s.Value == slices[0].Value) && slices.All(s =>
                { var matches = s.BitOffset == position; position += s.BitWidth; return matches; }))
                return new(bits, type, new SliceExpression(slices[0].Value, slices[0].BitOffset, values.Sum(v => v.Bits.Width)));
        }
        return new(bits, type, new ComposeExpression(values.Select(v => v.Expression).ToArray(), values.Select(v => v.Bits.Width).ToArray()));
    }
    public static NativeValue LoadStack(NativeState state, RegionId region, long offset, int size)
    {
        var bits = state.Stack.Load(new(region, offset), size);
        var parts = new List<NativeValue>();
        var end = checked(offset + size);
        while (offset < end)
        {
            var candidates = state.StackViews.Where(p => p.Key <= offset && p.Key + p.Value.Bits.Width / 8 > offset).ToArray();
            if (candidates.Length != 1) return new(bits, "unknown", new UnknownExpression($"stack:{offset}"));
            var view = candidates[0];
            var count = checked((int)Math.Min(end - offset, view.Key + view.Value.Bits.Width / 8 - offset));
            parts.Add(Slice(view.Value, checked((int)(offset - view.Key) * 8), count * 8));
            offset += count;
        }
        var result = Compose(parts.ToArray(), parts.Count == 1 ? parts[0].Type : "native-bits");
        var matches = result.Bits.Width == bits.Width && Enumerable.Range(0, size)
            .All(index => BitOps.Slice(result.Bits, index * 8, 8) == BitOps.Slice(bits, index * 8, 8));
        return matches ? result : new(bits, "unknown", new UnknownExpression("stack-view-invalidated"));
    }
}
