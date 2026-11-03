namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>字段访问：可访问时为字段本身，否则记为待证，由模板层按访问器或多语句内联的逆证明，证明不成立时记为洞。</summary>
    private ManagedValue FieldAccess(ManagedValue receiver, FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new FieldValue(receiver, field, type, Width(type));
        return fields.Accessible(field, receiver.Type) ? value
            : value with { Pending = new(address, $"内存 字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问", write) };
    }

    private ManagedValue StaticFieldAccess(FieldRef field, TypeRef type, bool write, ulong address)
    {
        var value = new StaticFieldValue(field, type, Width(type));
        return fields.Accessible(field, null) ? value
            : value with { Pending = new(address, $"内存 静态字段 {field.Field.Owner.FullName}.{field.Field.Name} 对调用方不可访问", write) };
    }
}
