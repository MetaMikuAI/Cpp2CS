
namespace Cpp2CS.Managed;

/// <summary>属性元数据中的单字段访问器：L3 严格形态或自动属性语言定义；写出和执行证据由恢复闭包另行检查。</summary>
public sealed record FieldAccessor(MethodRef Method, FieldRef Field, TypeRef ValueType, int Width, bool Write)
{
    /// <summary>字段与访问器的编译器特性、属性关联和签名符合自动属性语言定义；不是执行验证标记。</summary>
    public bool LanguageDefined { get; init; }

    public static FieldRef? FieldOf(ManagedValue value) => value switch { FieldValue f => f.Field, StaticFieldValue f => f.Field, _ => null };
    public static TypeRef? ReceiverType(ManagedValue value) => value is FieldValue f ? f.Receiver.Type : null;

    /// <summary>注解的签名、接收者和访问权限必须与当前字段操作一致。</summary>
    public bool Matches(ManagedTypes types, TypeDef caller, ManagedValue value, bool write) => Write == write
        && Field.Equals(FieldOf(value)) && ValueType.Equals(value.Type) && Width == value.Width
        && (value is StaticFieldValue ? Method.Method.IsStatic : value is FieldValue f && !Method.Method.IsStatic && (types.IsAssignable(f.Receiver.Type, Method.DeclaringType)
            || Method.Method.Owner.IsValueType && f.Receiver.Type is ByRefRef { Element: var element } && element.Equals(Method.DeclaringType)))
        && ManagedAccess.Method(types, caller, Method, ReceiverType(value));

}
