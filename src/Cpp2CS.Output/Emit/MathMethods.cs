using Cpp2CS.Managed;
using Cpp2CS.Model;

namespace Cpp2CS.Output;

/// <summary>浮点一元运算对应的 System.Math 方法；匹配的核心库裁剪掉该方法时返回空。</summary>
public static class MathMethods
{
    public static bool Uses(UnaryValue value) => CilOperators.Math(value.Op) is not null;
    public static MethodRef? Find(ManagedTypes types, UnaryValue value) => CilOperators.Math(value.Op) is not { } name ? null
        : types.CorlibMethod("System.Math", name, value.Op == UnaryOperator.Abs && value.Width == 32 ? types.Single : types.Double);
}
