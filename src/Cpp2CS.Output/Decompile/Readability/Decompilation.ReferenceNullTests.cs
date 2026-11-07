using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;
using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 类型重载了相等运算符时，反编译器把引用判空写成 (object)x == null。
    /// C# 9 的 x is null、x is not null 同样不调用运算符，优化编译的结果相同。值类型的装箱比较没有这种写法，保持原样。
    /// </summary>
    private sealed class ReferenceNullTests : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var test in rootNode.Descendants.OfType<BinaryOperatorExpression>().ToArray())
            {
                if (test.Operator is not (BinaryOperatorType.Equality or BinaryOperatorType.InEquality) || test.Right is not NullReferenceExpression) continue;
                if (test.Left is not CastExpression { Type: PrimitiveType { KnownTypeCode: KnownTypeCode.Object } } cast) continue;
                var type = cast.Expression.GetResolveResult().Type;
                if (type.IsReferenceType != true && type.Kind != TypeKind.TypeParameter) continue;
                var operand = cast.Expression;
                operand.Remove();
                Expression pattern = new NullReferenceExpression();
                if (test.Operator == BinaryOperatorType.InEquality) pattern = new UnaryOperatorExpression(UnaryOperatorType.PatternNot, pattern);
                test.ReplaceWith(new BinaryOperatorExpression(operand, BinaryOperatorType.IsPattern, pattern));
            }
        }
    }
}
