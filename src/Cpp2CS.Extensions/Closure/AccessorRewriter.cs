
namespace Cpp2CS.Extensions.Closure;

/// <summary>在原字段求值位置标明已证明的访问器；不搬动表达式、边赋值或接收者/值的求值顺序。</summary>
public static class AccessorRewriter
{
    public static ManagedBody Rewrite(ManagedBody body, Func<ManagedValue, bool, FieldAccessor?> select)
    {
        ManagedValue Value(ManagedValue value, bool write = false)
        {
            var accessor = value is FieldValue or StaticFieldValue ? select(value, write) : null;
            return value switch
            {
                // 读取值类型的子字段只需要值；已证明的整值 getter 可替代中间字段的取址。
                FieldValue { Receiver: AddressValue { Target: FieldValue component } } f when !write
                    && component.Type is Cpp2CS.Model.DefinitionRef { Definition.IsValueType: true }
                    && select(component, false) is not null => f with { Receiver = Value(component), Accessor = accessor },
                FieldValue f => f with { Receiver = Value(f.Receiver), Accessor = accessor },
                StaticFieldValue f => f with { Accessor = accessor },
                // F3 的结构体形态。取地址处（ldflda/ldsflda）不能认回：getter 只给出值，不给出存储位置；只改写其中的子值
                AddressValue a => a with
                {
                    Target = a.Target switch
                    {
                        FieldValue f => f with { Receiver = Value(f.Receiver) },
                        StaticFieldValue => a.Target,
                        _ => Value(a.Target),
                    }
                },
                _ => ManagedValues.Map(value, v => Value(v)),
            };
        }
        return ManagedValues.Map(body, v => Value(v), v => Value(v, true));
    }
}
