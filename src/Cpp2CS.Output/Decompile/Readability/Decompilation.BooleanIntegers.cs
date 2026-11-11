using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Syntax.PatternMatching;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// IL 里 bool 就是 0 和 1，恢复出的代码常把它扩展后再和常量比较或按位运算，反编译器写成 (c ? 1u : 0u) == (byte)0。
    /// 取值只有 0、1 的整数表达式和 0、1 比较时，写回条件本身。bool 的 &amp;、|、^ 不短路，求值次序和整数运算相同。
    /// </summary>
    private sealed class BooleanIntegers : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            // 改写时会复制子树：先处理内层，复制到的才是改好的节点。
            foreach (var test in rootNode.Descendants.OfType<BinaryOperatorExpression>().Reverse().ToArray())
                if (test.Operator is BinaryOperatorType.Equality or BinaryOperatorType.InEquality) Rewrite(test);
            foreach (var conditional in rootNode.Descendants.OfType<ConditionalExpression>().ToArray()) AsFold(conditional);
        }

        private static void Rewrite(BinaryOperatorExpression test)
        {
            var equal = test.Operator == BinaryOperatorType.Equality;
            Expression? result = null;
            if (Constant(test.Right) is { } constant and (0 or 1) && Condition(test.Left, shifted: true) is { } condition)
                result = equal == (constant == 1) ? condition : Negated(condition);
            else if (Condition(test.Left, shifted: false) is { } left && Condition(test.Right, shifted: false) is { } right)
                result = new BinaryOperatorExpression(left, test.Operator, right);
            if (result is not null) test.ReplaceWith(result);
        }

        /// <summary>取值为 0 或 1 的整数表达式对应的条件；shifted 时左移后和 0 比较的也算（非零与否不变）。</summary>
        private static Expression? Condition(Expression? expression, bool shifted)
        {
            switch (expression)
            {
                case ParenthesizedExpression parenthesized:
                    return Condition(parenthesized.Expression, shifted);
                case CastExpression { Type: PrimitiveType { KnownTypeCode: var code } } cast when IsInteger(code):
                    return Condition(cast.Expression, shifted: false);
                case ConditionalExpression conditional when Constant(conditional.TrueExpression) is (0 or 1) and var yes && Constant(conditional.FalseExpression) is (0 or 1) and var no && yes != no:
                    return yes == 1 ? conditional.Condition.Clone() : Negated(conditional.Condition.Clone());
                case BinaryOperatorExpression { Operator: BinaryOperatorType.BitwiseAnd, Right: var mask, Left: var masked } when Constant(mask) == 1 && Condition(masked, shifted: false) is { } inner:
                    return inner;
                case BinaryOperatorExpression { Operator: BinaryOperatorType.BitwiseAnd or BinaryOperatorType.BitwiseOr or BinaryOperatorType.ExclusiveOr } binary
                    when Condition(binary.Left, shifted: false) is { } left && Condition(binary.Right, shifted: false) is { } right:
                    return new BinaryOperatorExpression(left, binary.Operator, right);
                case BinaryOperatorExpression { Operator: BinaryOperatorType.ShiftLeft, Left: var value, Right: var amount } when shifted && Constant(amount) is >= 0 and < 32 && Condition(value, shifted: false) is { } moved:
                    return moved;
                default:
                    return null;
            }
        }

        private static bool IsInteger(KnownTypeCode code) => code is KnownTypeCode.Byte or KnownTypeCode.SByte or KnownTypeCode.Int16 or KnownTypeCode.UInt16 or KnownTypeCode.Int32 or KnownTypeCode.UInt32 or KnownTypeCode.Int64 or KnownTypeCode.UInt64;

        private static long? Constant(Expression? expression) => expression switch
        {
            ParenthesizedExpression parenthesized => Constant(parenthesized.Expression),
            CastExpression { Type: PrimitiveType { KnownTypeCode: var code } } cast when IsInteger(code) => Constant(cast.Expression),
            PrimitiveExpression { Value: byte or sbyte or short or ushort or int or uint or long } primitive => Convert.ToInt64(primitive.Value),
            _ => null,
        };

        private static Expression Negated(Expression condition)
        {
            condition.Remove();
            return GotoCleanup.Negate(condition);
        }

        /// <summary>x is T ? x as T : null 就是 x as T；x 是局部或字段时重复读取没有副作用。</summary>
        private static void AsFold(ConditionalExpression conditional)
        {
            if (conditional.FalseExpression is not NullReferenceExpression) return;
            if (conditional.Condition is not IsExpression { Expression: var tested, Type: var type } || conditional.TrueExpression is not AsExpression { Expression: var converted, Type: var target }) return;
            if (!SideEffectFree(tested) || !tested.IsMatch(converted) || !type.IsMatch(target)) return;
            conditional.ReplaceWith(conditional.TrueExpression.Clone());
        }

        private static bool SideEffectFree(Expression expression) => expression switch
        {
            IdentifierExpression or ThisReferenceExpression => expression.GetSymbol() is not IProperty and not IMethod,
            MemberReferenceExpression { Target: var target } => expression.GetSymbol() is IField { IsStatic: false } && SideEffectFree(target),
            _ => false,
        };
    }
}
