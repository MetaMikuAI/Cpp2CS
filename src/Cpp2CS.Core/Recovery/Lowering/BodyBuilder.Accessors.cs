namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>
    /// 字段访问：可访问时为字段本身，否则为被内联的访问器；都不成立时留待多语句内联的逆证明，
    /// 证明不成立时记为洞。
    /// </summary>
    private ManagedValue FieldAccess(ManagedValue receiver, FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new FieldValue(receiver, field, type, Width(type));
        if (fields.Accessible(field, receiver.Type)) return value;
        return fields.Accessor(field, type, write, receiver.Type) is { } accessor ? value with { Accessor = accessor }
            : value with { Pending = (address, $"内存 字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问，没有可证明的访问器（{fields.Failure(field, type, write, receiver.Type)}），也不在可证明的内联方法体中") };
    }

    private ManagedValue StaticFieldAccess(FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new StaticFieldValue(field, type, Width(type));
        if (fields.Accessible(field, null)) return value;
        return fields.Accessor(field, type, write, null) is { } accessor ? value with { Accessor = accessor }
            : Hole(address, $"内存 静态字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问，没有可证明的访问器（{fields.Failure(field, type, write, null)}）", type);
    }
}
