using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed class CompilerScaffolding : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            if (!rootNode.Descendants.Any(n => n is SimpleType { Identifier: "Await" or "Unrecovered" }
                or IdentifierExpression { Identifier: "Await" or "Unrecovered" }))
                foreach (var import in rootNode.Descendants.OfType<UsingDeclaration>().Where(u => u.Namespace == "Cpp2CS").ToArray()) import.Remove();
            // 异步 builder 的故障转发已由 async 承担；无副作用的原样重抛不需要再包一层。
            foreach (var guarded in rootNode.Descendants.OfType<TryCatchStatement>().ToArray())
                if (guarded.FinallyBlock is null && guarded.CatchClauses.ToArray() is [var catcher]
                    && catcher.Condition is null && catcher.Body?.Statements.Where(s => s is not EmptyStatement).ToArray() is [ThrowStatement { Expression: null }]
                    && guarded.TryBlock is { } body) guarded.ReplaceWith(body.Clone());
            foreach (var method in rootNode.Descendants.OfType<MethodDeclaration>())
                if (method.Body?.Statements.ToArray() is [BlockStatement content]) method.Body = (BlockStatement)content.Clone();

            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray())
                if (declaration.Variables.ToArray() is [var variable] && variable.Initializer is NullReferenceExpression
                    && declaration.GetParent<MethodDeclaration>() is { } method
                    && !method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == variable.Name)) declaration.Remove();

            // 只有所有引用都已展开成捕获变量后，才能移除残留的闭包类型声明。
            foreach (var type in rootNode.Descendants.OfType<TypeDeclaration>().Reverse().ToArray())
            {
                if (type.Parent is not TypeDeclaration || !type.Modifiers.HasFlag(Modifiers.Private)
                    || !type.Name.Contains("DisplayClass", StringComparison.Ordinal)
                    || !type.Attributes.SelectMany(s => s.Attributes).Any(a => a.Type.ToString() is "CompilerGenerated" or "CompilerGeneratedAttribute")) continue;
                if (rootNode.Descendants.Where(n => !n.Ancestors.Contains(type)).Any(n => n switch
                {
                    SimpleType reference => reference.Identifier == type.Name,
                    MemberType reference => reference.MemberName == type.Name,
                    IdentifierExpression reference => reference.Identifier == type.Name,
                    _ => false,
                })) continue;
                type.Remove();
            }
        }
    }
}
