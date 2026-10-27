using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private static void RewriteInjectedCalls(AstNode root, TransformContext context)
    {
        static AstType SystemType(params string[] names)
        {
            AstType result = new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true };
            foreach (var name in names) result = new MemberType(result, name);
            return result;
        }
        static Expression Flag(string name) => new MemberReferenceExpression(new TypeReferenceExpression(SystemType("Reflection", "BindingFlags")), name);
        static Expression Flags(params string[] names) => names.Select(Flag).Aggregate((a, b) => new BinaryOperatorExpression(a, BinaryOperatorType.BitwiseOr, b));
        bool Accessible(IType type) => type.GetDefinition() is { } d
            && (d.Accessibility == Accessibility.Public || d.Accessibility == Accessibility.Internal && d.ParentModule == context.TypeSystem.MainModule)
            && (d.DeclaringTypeDefinition is null || Accessible(d.DeclaringTypeDefinition));
        Expression? TypeObject(IType type, AstType syntax)
        {
            if (Accessible(type)) return new TypeOfExpression(syntax.Clone());
            if (type.GetDefinition() is not { DeclaringTypeDefinition: { } parent, TypeParameterCount: 0 } definition
                || syntax is not MemberType member || TypeObject(parent, member.Target) is not { } outer) return null;
            return new InvocationExpression(new MemberReferenceExpression(outer, "GetNestedType"),
                new PrimitiveExpression(definition.Name), Flags("Public", "NonPublic"));
        }
        foreach (var generated in root.Descendants.OfType<TypeDeclaration>())
        {
            if (generated.GetSymbol() is not ITypeDefinition owner || !owner.GetAttributes()
                .Any(a => a.AttributeType.FullName == "Unity.Jobs.DOTSCompilerGeneratedAttribute")) continue;
            foreach (var call in generated.Descendants.OfType<InvocationExpression>().ToArray())
            {
                if (call.Arguments.Count != 0 || call.GetSymbol() is not IMethod { IsStatic: true, Accessibility: Accessibility.Public, Parameters.Count: 0 } method
                    || method.ReturnType.Kind != TypeKind.Void || method.TypeArguments.Count == 0 || method.TypeArguments.All(Accessible)
                    || call.Target is not MemberReferenceExpression { Target: TypeReferenceExpression declaring } target
                    || target.TypeArguments.Count != method.TypeArguments.Count || !Accessible(method.DeclaringType)
                    || method.DeclaringTypeDefinition!.Methods.Count(m => m.Name == method.Name && m.IsStatic && m.Accessibility == Accessibility.Public) != 1) continue;
                var arguments = method.TypeArguments.Zip(target.TypeArguments, TypeObject).ToArray();
                if (arguments.Any(a => a is null)) continue;
                var lookup = new InvocationExpression(new MemberReferenceExpression(new TypeOfExpression(declaring.Type.Clone()), "GetMethod"),
                    new PrimitiveExpression(method.Name), Flags("Public", "Static", "DeclaredOnly"));
                var closed = new InvocationExpression(new MemberReferenceExpression(lookup, "MakeGenericMethod"), arguments.Select(a => a!));
                var action = SystemType("Action");
                var bound = new InvocationExpression(new MemberReferenceExpression(closed, "CreateDelegate"), new TypeOfExpression(action.Clone()));
                // 委托直接调用保留原异常；MethodInfo.Invoke 会额外包裹 TargetInvocationException。
                call.ReplaceWith(new InvocationExpression(new ParenthesizedExpression(new CastExpression(action, bound))));
            }
            foreach (var expression in generated.Descendants.OfType<TypeOfExpression>().ToArray())
                if (expression.Type.Annotation<ResolveResult>()?.Type is { } type && !Accessible(type) && TypeObject(type, expression.Type) is { } replacement)
                    expression.ReplaceWith(replacement);
        }
    }
}
