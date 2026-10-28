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
            RewriteInjectedCalls(rootNode, context);
            // 类型与分支事实归约后，局部值上的空判断没有可观察效果。
            static bool PureCondition(Expression? expression) => expression is PrimitiveExpression or NullReferenceExpression
                || expression is IdentifierExpression id && id.GetILVariable() is not null
                || expression is UnaryOperatorExpression { Operator: UnaryOperatorType.Not } negated
                    && negated.Annotation<OperatorResolveResult>() is { UserDefinedOperatorMethod: null } && PureCondition(negated.Expression)
                || expression is BinaryOperatorExpression { Operator: BinaryOperatorType.Equality or BinaryOperatorType.InEquality
                    or BinaryOperatorType.ConditionalAnd or BinaryOperatorType.ConditionalOr } binary
                    && binary.Annotation<OperatorResolveResult>() is { UserDefinedOperatorMethod: null }
                    && PureCondition(binary.Left) && PureCondition(binary.Right);
            static bool Empty(Statement? statement) => statement is null or EmptyStatement || statement is BlockStatement { Statements.Count: 0 };
            foreach (var condition in rootNode.Descendants.OfType<IfElseStatement>().Reverse().ToArray())
                if (Empty(condition.TrueStatement) && Empty(condition.FalseStatement)
                    && condition.Condition.Annotation<ResolveResult>()?.Type.FullName == "System.Boolean" && PureCondition(condition.Condition)) condition.Remove();
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
                if (declaration.Variables.ToArray() is not [var variable]
                    || variable.GetILVariable() is not { IsSingleDefinition: true, UsesInitialValue: false, Type.IsReferenceType: true } local
                    || local.AddressInstructions.Count != 0) continue;
                var references = rootNode.Descendants.OfType<IdentifierExpression>().Where(id => id.GetILVariable() == local).ToArray();
                var receiver = variable.Initializer as ThisReferenceExpression;
                ExpressionStatement? separateStore = null;
                if (receiver is null && variable.Initializer is null)
                {
                    var writes = references.Where(id => id.Parent is AssignmentExpression assignment && assignment.Left == id).ToArray();
                    if (writes is not [var target] || target.Parent is not AssignmentExpression
                        { Operator: AssignmentOperatorType.Assign, Right: ThisReferenceExpression instance, Parent: ExpressionStatement statement }) continue;
                    receiver = instance;
                    separateStore = statement;
                    references = references.Where(id => id != target).ToArray();
                }
                if (receiver?.Annotation<ResolveResult>()?.Type.Equals(local.Type) != true) continue;
                if (references.Any(id => id.Parent is DirectionExpression
                    || id.Parent is AssignmentExpression assignment && assignment.Left == id
                    || id.Ancestors.OfType<InvocationExpression>().Any(call => call.Target is IdentifierExpression { Identifier: "nameof" }))) continue;
                foreach (var reference in references) reference.ReplaceWith(receiver.Clone());
                separateStore?.Remove();
                declaration.Remove();
            }
            if (!rootNode.Descendants.Any(n => n is SimpleType { Identifier: "Await" or "Unrecovered" or "NativeImports" }
                or IdentifierExpression { Identifier: "Await" or "Unrecovered" or "NativeImports" }))
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

            var expanded = rootNode.Descendants.Where(n => n is LambdaExpression or AnonymousMethodExpression)
                .SelectMany(n => n.Annotations.OfType<ILFunction>()).Where(f => f.Method is not null)
                .Select(f => f.Method!.MemberDefinition).Concat(rootNode.Annotation<ExpandedLambdaOrigins>()?.Methods ?? Array.Empty<IMember>()).ToHashSet();
            // 缓存类仅初始化空实例和委托字段；有显式构造逻辑或未展开方法时保留读取。
            var caches = rootNode.Descendants.OfType<TypeDeclaration>().Where(type =>
                type.Parent is TypeDeclaration && type.Modifiers.HasFlag(Modifiers.Private)
                && type.GetSymbol() is ITypeDefinition definition && (definition.Name == "<>c" || definition.Name.StartsWith("<>c__", StringComparison.Ordinal))
                && definition.GetAttributes().Any(a => a.AttributeType.FullName == "System.Runtime.CompilerServices.CompilerGeneratedAttribute")
                && type.Members.All(m => m is FieldDeclaration or MethodDeclaration)
                && type.Members.OfType<MethodDeclaration>().All(m => m.GetSymbol() is IMethod method && expanded.Contains(method.MemberDefinition))
                && type.Members.OfType<FieldDeclaration>().All(f => f.Variables.ToArray() is [var v] && f.GetSymbol() is IField { IsStatic: true } field
                    && (field.Name.StartsWith("<>9__", StringComparison.Ordinal) && field.ReturnType.Kind == TypeKind.Delegate
                        && v.Initializer is null or NullReferenceExpression
                        || field.Name == "<>9" && v.Initializer is ObjectCreateExpression { Arguments.Count: 0, Initializer: null } creation
                            && creation.Type.Annotation<ResolveResult>()?.Type.GetDefinition()?.Equals(definition) == true)))
                .Select(t => (ITypeDefinition)t.GetSymbol()!).ToHashSet();
            bool CacheRead(Expression? expression) => expression?.GetSymbol() is IField { IsStatic: true } field
                && field.Name.StartsWith("<>9__", StringComparison.Ordinal) && field.DeclaringTypeDefinition is { } owner && caches.Contains(owner);
            // lambda 已展开后，未使用的缓存读取不再维持辅助类的引用。
            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray())
                if (declaration.Variables.ToArray() is [var variable] && CacheRead(variable.Initializer)
                    && variable.GetILVariable() is { IsSingleDefinition: true } local && local.AddressInstructions.Count == 0
                    && !rootNode.Descendants.OfType<IdentifierExpression>().Any(id => id.GetILVariable() == local)) declaration.Remove();
            foreach (var statement in rootNode.Descendants.OfType<ExpressionStatement>().ToArray())
                if (statement.Expression is AssignmentExpression { Operator: AssignmentOperatorType.Assign,
                        Left: IdentifierExpression { Identifier: "_" } discard } assignment
                    && discard.GetILVariable() is null && CacheRead(assignment.Right)) statement.Remove();
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
