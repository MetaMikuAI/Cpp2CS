using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed class CompilerScaffolding : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            // Unity 的 IL 后处理器可注入跨程序集 internal 标记，C# 无法直接声明它。
            foreach (var attribute in rootNode.Descendants.OfType<ICSharpCode.Decompiler.CSharp.Syntax.Attribute>().ToArray())
            {
                if (attribute.Arguments.Count != 0 || attribute.Type.Annotation<ResolveResult>()?.Type.GetDefinition() is not
                    {
                        FullName: "Unity.Jobs.DOTSCompilerGeneratedAttribute",
                        Accessibility: Accessibility.Internal
                    } marker || marker.ParentModule == context.TypeSystem.MainModule
                    || attribute.Parent is not AttributeSection { Parent: { } owner } section) continue;
                owner.AddLeadingTrivia(new Comment($" IL 后处理器标记：[{attribute}]；原始特性保留在恢复程序集。"));
                attribute.Remove();
                if (section.Attributes.Count == 0) section.Remove();
            }
            // 类实例的单一定义副本仍是同一个 this；按 IL 变量身份替换，包括 lambda 中的捕获。
            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray())
            {
                if (declaration.Variables.ToArray() is not [var variable] || variable.Initializer is not ThisReferenceExpression receiver
                    || variable.GetILVariable() is not { IsSingleDefinition: true, UsesInitialValue: false, Type.IsReferenceType: true } local
                    || local.AddressInstructions.Count != 0 || receiver.Annotation<ResolveResult>()?.Type.Equals(local.Type) != true) continue;
                var references = rootNode.Descendants.OfType<IdentifierExpression>().Where(id => id.GetILVariable() == local).ToArray();
                if (references.Any(id => id.Parent is DirectionExpression
                    || id.Parent is AssignmentExpression assignment && assignment.Left == id
                    || id.Ancestors.OfType<InvocationExpression>().Any(call => call.Target is IdentifierExpression { Identifier: "nameof" }))) continue;
                foreach (var reference in references) reference.ReplaceWith(receiver.Clone());
                declaration.Remove();
            }
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

            // lambda 已展开后，不再使用的编译器委托缓存读取不能继续维持闭包类型的引用。
            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray())
                if (declaration.Variables.ToArray() is [var variable] && variable.Initializer?.GetSymbol() is IField { IsStatic: true } field
                    && field.Name.StartsWith("<>9__", StringComparison.Ordinal)
                    && field.DeclaringTypeDefinition?.GetAttributes().Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute") == true
                    && variable.GetILVariable() is { IsSingleDefinition: true } local && local.AddressInstructions.Count == 0
                    && !rootNode.Descendants.OfType<IdentifierExpression>().Any(id => id.GetILVariable() == local)) declaration.Remove();

            var expanded = rootNode.Descendants.Where(n => n is LambdaExpression or AnonymousMethodExpression)
                .SelectMany(n => n.Annotations.OfType<ILFunction>()).Where(f => f.Method is not null)
                .Select(f => f.Method!.MemberDefinition).ToHashSet();
            // 只有所有引用都已展开成捕获变量后，才能移除残留的闭包类型声明。
            foreach (var type in rootNode.Descendants.OfType<TypeDeclaration>().Reverse().ToArray())
            {
                if (type.Parent is not TypeDeclaration || !type.Modifiers.HasFlag(Modifiers.Private)
                    || !type.Attributes.SelectMany(s => s.Attributes).Any(a => a.Type.ToString() is "CompilerGenerated" or "CompilerGeneratedAttribute")) continue;
                if (!type.Name.Contains("DisplayClass", StringComparison.Ordinal)
                    && (type.GetSymbol() is not ITypeDefinition definition || definition.Name != "<>c" && !definition.Name.StartsWith("<>c__", StringComparison.Ordinal)
                        || type.Members.OfType<MethodDeclaration>().Any(m => m.GetSymbol() is not IMethod method || !expanded.Contains(method.MemberDefinition)))) continue;
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
