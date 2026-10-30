using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>事件与后备字段重名时，泛型字段引用按原始字段定义使用声明的消歧名称。</summary>
    private sealed class EventFieldNames : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            var names = new Dictionary<IMember, string>();
            foreach (var declaration in rootNode.Descendants.OfType<FieldDeclaration>())
                foreach (var variable in declaration.Variables)
                    if ((variable.GetSymbol() ?? declaration.GetSymbol()) is IField field && variable.Name != field.Name
                        && declaration.Parent is TypeDeclaration owner
                        && owner.Members.OfType<CustomEventDeclaration>().Any(e => e.Name == field.Name))
                        names[field.MemberDefinition] = variable.Name;
            foreach (var expression in rootNode.Descendants.OfType<Expression>())
            {
                if (expression.GetSymbol() is not IField field || !names.TryGetValue(field.MemberDefinition, out var name)) continue;
                if (expression is MemberReferenceExpression member) member.MemberName = name;
                else if (expression is IdentifierExpression identifier) identifier.Identifier = name;
            }
        }
    }
}
