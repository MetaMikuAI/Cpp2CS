using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>变换阶段加入的类型不再经过 using 分析：一律写全名。</summary>
    private static readonly ICSharpCode.Decompiler.CSharp.Syntax.TypeSystemAstBuilder QualifiedTypes = new();

    /// <summary>不同的局部同名时，内层声明不能遮蔽外层（CS0136），同一作用域不能重复（CS0128）：给后者换名字。</summary>
    private sealed class ShadowedLocals : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var body in rootNode.Descendants.OfType<BlockStatement>().Where(b => b.Parent is EntityDeclaration or Accessor))
            {
                var variables = body.Descendants.OfType<VariableInitializer>().Where(v => v.Parent is VariableDeclarationStatement).ToArray();
                var occupied = variables.Select(v => v.Name).ToHashSet();
                foreach (var group in variables.GroupBy(v => v.Name).Where(g => g.Count() > 1))
                {
                    var scopes = group.Select(v => (Variable: v, Scope: Scope(v))).ToArray();
                    for (var i = 0; i < scopes.Length; i++)
                    {
                        var (variable, scope) = scopes[i];
                        var conflict = scopes.Where((other, j) => j != i).Any(other => other.Scope != scope && other.Scope.Descendants.Contains(scope))
                            || scopes.Take(i).Any(other => other.Scope == scope);
                        if (!conflict) continue;
                        var suffix = 2;
                        string name;
                        do name = group.Key + "Local" + suffix++; while (!occupied.Add(name));
                        var local = variable.GetILVariable();
                        var references = scope.Descendants.OfType<IdentifierExpression>().Where(id => id.Identifier == group.Key && (local is null || id.GetILVariable() == local));
                        foreach (var reference in references.ToArray()) reference.Identifier = name;
                        variable.Name = name;
                    }
                }
            }
            foreach (var lambda in rootNode.Descendants.OfType<LambdaExpression>()) LambdaParameters(lambda);
        }

        /// <summary>闭包展开后，lambda 形参和捕获的外层变量可能同名：外层变量读到的会变成形参。给形参换名字。</summary>
        private static void LambdaParameters(LambdaExpression lambda)
        {
            foreach (var parameter in lambda.Parameters)
            {
                if (parameter.Name is not { } parameterName) continue;
                var uses = lambda.Body.DescendantsAndSelf.OfType<IdentifierExpression>().Where(i => i.Identifier == parameterName).ToArray();
                var variables = uses.Select(u => u.GetILVariable()).Where(v => v is not null).Distinct().ToArray();
                if (variables.Length < 2 || lambda.Annotation<ILFunction>() is not { } function) continue;
                var own = variables.FirstOrDefault(v => v!.Kind == VariableKind.Parameter && v.Function == function);
                if (own is null) continue;
                var name = parameterName + "Parameter";
                foreach (var use in uses.Where(u => u.GetILVariable() == own)) use.Identifier = name;
                parameter.Name = name;
            }
        }

        /// <summary>局部的作用域：所在的块、switch 或 using 声明的外层块。</summary>
        private static AstNode Scope(VariableInitializer variable)
        {
            var declaration = variable.Parent!;
            return declaration.Parent is UsingStatement { IsEnhanced: true } @using ? @using.Parent! : declaration.Parent is ICSharpCode.Decompiler.CSharp.Syntax.SwitchSection section ? section.Parent! : declaration.Parent!;
        }
    }

    /// <summary>闭包展开后，不同类型的同名 IL 局部变量不能由声明变换合并。</summary>
    private sealed class DistinctLocalNames : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var method in rootNode.Descendants.OfType<EntityDeclaration>().Where(n => n is MethodDeclaration or ConstructorDeclaration))
            {
                var references = method.Descendants.OfType<IdentifierExpression>().Where(id => id.GetILVariable() is not null).ToArray();
                var variables = references.Select(id => id.GetILVariable()!).Distinct().ToArray();
                var occupied = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier).ToHashSet();
                foreach (var group in variables.GroupBy(v => v.Name))
                {
                    if (group.Select(v => v.Type).Distinct().Count() <= 1) continue;
                    foreach (var variable in group.OrderBy(v => v.Kind == VariableKind.Parameter ? 0 : 1).Skip(1))
                    {
                        if (variable.Kind == VariableKind.Parameter) continue;
                        var suffix = 2;
                        string name;
                        do name = group.Key + "Local" + suffix++; while (!occupied.Add(name));
                        variable.Name = name;
                        foreach (var reference in references.Where(id => id.GetILVariable() == variable)) reference.Identifier = name;
                        foreach (var loop in method.Descendants.OfType<ForeachStatement>().Where(l => l.VariableDesignation is SingleVariableDesignation d && d.Identifier == group.Key && l.EmbeddedStatement.Descendants.Contains(references.FirstOrDefault(id => id.GetILVariable() == variable)))) ((SingleVariableDesignation)loop.VariableDesignation!).Identifier = name;
                        foreach (var declaration in method.Descendants.OfType<VariableInitializer>().Where(v => v.GetILVariable() == variable)) declaration.Name = name;
                    }
                }
            }
        }
    }
}
