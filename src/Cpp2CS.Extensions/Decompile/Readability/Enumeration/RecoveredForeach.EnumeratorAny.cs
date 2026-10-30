using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Extensions.Decompile;

internal sealed partial class RecoveredForeach
{
    private static void RecoverAny(AstNode root, ICompilation compilation)
    {
        if (!compilation.Modules.SelectMany(m => m.TopLevelTypeDefinitions).Where(t => t.FullName == "System.Linq.Enumerable"
                && t.ParentModule?.AssemblyName is "System.Core" or "System.Linq")
            .SelectMany(t => t.Methods).Any(m => m.Name == "Any" && m.IsStatic && m.Accessibility == Accessibility.Public
                && m.TypeParameters.Count == 1 && m.Parameters.Count == 1 && m.ReturnType.FullName == "System.Boolean")) return;
        static Expression? Strip(Expression? value)
        {
            while (value is ParenthesizedExpression or CastExpression { Type: PrimitiveType { Keyword: "byte" or "sbyte" or "short" or "ushort" or "int" or "uint" or "long" or "ulong" } })
                value = value is ParenthesizedExpression p ? p.Expression : ((CastExpression)value).Expression;
            return value;
        }
        static bool Result(Expression? expression, string name)
        {
            expression = Strip(expression);
            if (expression is BinaryOperatorExpression { Operator: BinaryOperatorType.InEquality, Left: var left, Right: var zero } && IntegerConstant(zero, 0)) expression = Strip(left);
            else return Name(expression, name);
            if (expression is BinaryOperatorExpression { Operator: BinaryOperatorType.BitwiseAnd, Left: var masked, Right: var one } && IntegerConstant(one, 1)) expression = Strip(masked);
            return Name(expression, name);
        }
        static AstType SystemType(string name) => new MemberType(new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true }, name);
        foreach (var method in root.Descendants.OfType<MethodDeclaration>().ToArray())
        {
            if (method.ReturnType is not PrimitiveType { Keyword: "bool" } || method.Body?.Statements.ToArray() is not
                [VariableDeclarationStatement declaration, ExpressionStatement
                {
                    Expression: AssignmentExpression
                    {
                        Operator: AssignmentOperatorType.Assign,
                        Left: IdentifierExpression enumerator, Right: InvocationExpression
                        {
                            Arguments.Count: 0,
                            Target: MemberReferenceExpression { MemberName: "GetEnumerator" } get
                        } factory
                    }
                },
                    VariableDeclarationStatement resultDeclaration, TryCatchStatement guarded, var dispose, ReturnStatement returned]
                || declaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression } variable] || variable.Name != enumerator.Identifier
                || resultDeclaration.Variables.ToArray() is not [{ Initializer: null } result]
                || guarded.FinallyBlock is not null || guarded.CatchClauses.ToArray() is not [var catcher]
                || catcher.Condition is not null || catcher.Type?.ToString() is not ("Exception" or "System.Exception")
                || catcher.Body?.Statements.ToArray() is not [var failureDispose, ThrowStatement thrown]
                || !Dispose(dispose, variable.Name) || !Dispose(failureDispose, variable.Name)
                || thrown.Expression is not null && !Name(thrown.Expression, catcher.VariableName)
                || guarded.TryBlock?.Statements.ToArray() is not [ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: var assigned, Right: var value } }]
                || !Name(assigned, result.Name) || !Result(returned.Expression, result.Name)) continue;
            if (value is ConditionalExpression { Condition: var condition, TrueExpression: var one, FalseExpression: var zero })
            {
                if (!IntegerConstant(one, 1) || !IntegerConstant(zero, 0)) continue;
                value = condition;
            }
            else if (resultDeclaration.Type is not PrimitiveType { Keyword: "bool" }) continue;
            if (value is not InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "MoveNext", Target: var receiver } }
                || !Name(receiver, variable.Name) || factory.GetSymbol() is not IMethod { DeclaringTypeDefinition: { } collection }) continue;
            // 标准集合的公开和接口枚举一致；自定义同名 GetEnumerator 不作此推断。
            if (collection.ParentModule?.AssemblyName is not ("mscorlib" or "System.Private.CoreLib" or "System.Collections")
                || collection.ReflectionName is not ("System.Collections.Generic.IEnumerable`1" or "System.Collections.Generic.List`1"
                    or "System.Collections.Generic.Dictionary`2+ValueCollection" or "System.Collections.Generic.Dictionary`2+KeyCollection")) continue;
            Expression source = get.Target.Clone();
            var nonnull = get.Target.GetSymbol() is IProperty { Name: "Values" or "Keys", DeclaringTypeDefinition: { } owner }
                && owner.ReflectionName == "System.Collections.Generic.Dictionary`2" && owner.ParentModule?.AssemblyName is "mscorlib" or "System.Private.CoreLib";
            // Any 对空源抛 ArgumentNullException；原实例调用抛 NullReferenceException。
            if (!nonnull) source = new BinaryOperatorExpression(source, BinaryOperatorType.NullCoalescing,
                new ThrowExpression(new ObjectCreateExpression(SystemType("NullReferenceException"))));
            var any = new MemberReferenceExpression(new TypeReferenceExpression(new MemberType(SystemType("Linq"), "Enumerable")), "Any");
            method.Body = new BlockStatement { new ReturnStatement(new InvocationExpression(any, source)) };
        }
    }
}
