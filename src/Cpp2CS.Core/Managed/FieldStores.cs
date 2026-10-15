using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

public sealed partial class ValueRecovery
{
    /// <summary>恢复原位置的写入；合并的数值字段写入按完整字段拆解，接收者和源值各求值一次。</summary>
    public IReadOnlyList<ManagedStatement>? Store(Store store, out string? problem)
    {
        if (Location(store.Target, store.Value.Width, out _, whole: true) is { } whole && types.Kind(whole.Type) == ValueKind.Struct
            && Recover(store.Value, out _) is { } source && source.Type == whole.Type && source.Width == whole.Width)
        {
            problem = null;
            return [new ManagedStore(store.Address, whole, source)];
        }
        if (Location(store.Target, store.Value.Width, out problem) is { } location)
            return RecoverAs(store.Value, location.Type, out problem) is { } stored
                ? [new ManagedStore(store.Address, location, stored)] : null;
        var originalProblem = problem;
        var width = store.Value.Width;
        if (width is not (16 or 32 or 64) || Metadata.StaticAddress(store.Target) is not null) return null;
        var address = store.Target;
        long offset = 0;
        if (address is Binary { Op: BinOp.Add, Right: Const c } add) { offset = c.Signed; address = add.Left; }
        ManagedValue? receiver;
        if (address is FrameAddress frame)
        {
            var root = Stack.Objects.SingleOrDefault(o => frame.Offset >= o.Offset && frame.Offset + width / 8 <= o.Offset + o.Width / 8);
            if (root is null) return null;
            receiver = root;
            offset = frame.Offset - root.Offset;
        }
        else receiver = Recover(address, out _);
        if (receiver is null || offset is < 0 or > int.MaxValue) return null;
        var type = receiver.Type is ByRefRef byRef ? byRef.Element : receiver.Type;
        if (receiver is not StackLocalValue && receiver.Type is not ByRefRef && !ManagedTypes.IsReferenceType(type)) return null;
        if (types.FieldSpan(type, (int)offset, width / 8) is not { Count: > 1 } parts) return null;
        var constant = store.Value as Const;
        // 非规范 bool 位型不能通过 C# bool 赋值往返；动态位型需另有范围证明。
        if (parts.Any(p => types.Kind(p.Type) == ValueKind.Bool && (constant is null || ((constant.Value >> ((p.Offset - (int)offset) * 8)) & 0xff) > 1)))
        { problem = "合并字段写入的布尔位型尚未证明"; return null; }
        if (Recover(store.Value, out problem) is not { } value) { problem ??= originalProblem; return null; }
        if (!Numeric(value.Type) || value.Width != width) { problem = originalProblem; return null; }
        var output = new List<ManagedStatement>();
        if (receiver is not (ArgumentValue or LocalValue or StackLocalValue))
        {
            var saved = Temporary(receiver.Type);
            output.Add(new ManagedAssignment(store.Address, saved, receiver)); receiver = saved;
        }
        if (constant is null)
        {
            var saved = Temporary(value.Type);
            output.Add(new ManagedAssignment(store.Address, saved, value)); value = saved;
        }
        foreach (var part in parts)
        {
            var bits = types.Size(part.Type) * 8;
            var shift = (part.Offset - (int)offset) * 8;
            ManagedValue piece;
            if (constant is not null) piece = new ConstantValue((constant.Value >> shift) & Expr.Mask(bits), part.Type, bits);
            else
            {
                if (aggregates.Project(value, shift / 8, bits) is not { } projected) { problem = originalProblem; return null; }
                piece = projected.Type == part.Type ? projected : new ConversionValue(ConvKind.Bitcast, projected, part.Type, bits);
            }
            var target = receiver;
            foreach (var field in part.Path)
            {
                var fieldType = field.Field.Type.Substitute(field.DeclaringType is DefinitionRef owner ? owner.Arguments : [], []);
                target = new FieldValue(target, field, fieldType, types.Size(fieldType) * 8);
            }
            output.Add(new ManagedStore(store.Address, target, piece));
        }
        problem = null;
        return output;
    }
}
