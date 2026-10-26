using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.IL;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
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
                        foreach (var declaration in method.Descendants.OfType<VariableInitializer>().Where(v => v.GetILVariable() == variable)) declaration.Name = name;
                    }
                }
            }
        }
    }
}
