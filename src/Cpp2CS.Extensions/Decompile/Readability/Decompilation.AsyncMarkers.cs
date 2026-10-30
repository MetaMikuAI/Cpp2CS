using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Extensions.Decompile;

public sealed partial class ReadabilityTransforms
{
    /// <summary>
    /// async 提升的标记（Cpp2CS.Await，见 EmissionSymbols.Awaits）改写成 C#：Of/Do → await，Result(x) → x，Completed() → 无值的 return；
    /// 最近的方法或匿名函数加 async，去掉 [AsyncStateMachine]、[DebuggerStepThrough] 与状态机的嵌套类型声明。
    /// </summary>
    private sealed class AsyncMarkers : IAstTransform
    {
        private static string Last(AstType type) => (type switch { SimpleType s => s.Identifier, MemberType m => m.MemberName, _ => null }) ?? "";

        public void Run(AstNode rootNode, TransformContext context)
        {
            var functions = new HashSet<AstNode>();
            // 外层 Result 会克隆参数；先转换内部 await，避免副本中残留标记。
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().Reverse().ToArray())
            {
                if (call.Target is not MemberReferenceExpression { Target: TypeReferenceExpression { Type: var type } } member || Last(type) != "Await"
                    || member.MemberName is not ("Of" or "Do" or "Result" or "Completed")) continue;
                // ILSpy 可能已经把编译器生成的方法展开为 lambda，标记属于最近的函数。
                if (call.Ancestors.FirstOrDefault(n => n is MethodDeclaration or LambdaExpression or AnonymousMethodExpression) is { } function) functions.Add(function);
                switch (member.MemberName)
                {
                    case "Of" or "Do": call.ReplaceWith(new UnaryOperatorExpression(UnaryOperatorType.Await, call.Arguments.First().Clone())); break;
                    case "Result": call.ReplaceWith(call.Arguments.First().Clone()); break;
                    default:
                        if (call.Parent is ReturnStatement) call.Remove();
                        else if (call.Parent is ExpressionStatement statement) statement.ReplaceWith(new ReturnStatement());
                        break;
                }
            }
            foreach (var function in functions)
            {
                IEnumerable<AttributeSection> attributes;
                BlockStatement? body;
                switch (function)
                {
                    case MethodDeclaration method:
                        method.Modifiers |= Modifiers.Async; attributes = method.Attributes; body = method.Body; break;
                    case LambdaExpression lambda:
                        lambda.IsAsync = true; attributes = lambda.Attributes; body = lambda.Body as BlockStatement; break;
                    case AnonymousMethodExpression anonymous:
                        anonymous.IsAsync = true; attributes = []; body = anonymous.Body; break;
                    default: continue;
                }
                if (body?.Statements.LastOrDefault() is ReturnStatement { Expression: null } last) last.Remove();
                foreach (var attribute in attributes.SelectMany(s => s.Attributes).ToArray())
                {
                    var name = Last(attribute.Type);
                    if (name is not ("AsyncStateMachine" or "AsyncStateMachineAttribute" or "DebuggerStepThrough" or "DebuggerStepThroughAttribute")) continue;
                    if (attribute.Arguments.FirstOrDefault() is TypeOfExpression { Type: var machine } && function.GetParent<TypeDeclaration>() is { } owner)
                    {
                        var container = machine is MemberType member ? owner.Members.OfType<TypeDeclaration>().FirstOrDefault(t => t.Name == Last(member.Target)) : owner;
                        if (container is not null)
                            foreach (var nested in container.Members.OfType<TypeDeclaration>().Where(t => t.Name == Last(machine)).ToArray()) nested.Remove();
                    }
                    attribute.Remove();
                }
                foreach (var section in attributes.Where(s => s.Attributes.Count == 0).ToArray()) section.Remove();
            }
        }
    }

}
