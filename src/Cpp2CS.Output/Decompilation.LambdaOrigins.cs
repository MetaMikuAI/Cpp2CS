using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed record ExpandedLambdaOrigins(IReadOnlyCollection<IMember> Methods);

    /// <summary>查询语法转换可能移除 lambda 节点，提前保留已展开方法的身份。</summary>
    private sealed class PreserveLambdaOrigins : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context) => rootNode.AddAnnotation(new ExpandedLambdaOrigins(
            rootNode.Descendants.Where(n => n is LambdaExpression or AnonymousMethodExpression)
                .SelectMany(n => n.Annotations.OfType<ILFunction>()).Where(f => f.Method is not null)
                .Select(f => f.Method!.MemberDefinition).ToHashSet()));
    }
}
