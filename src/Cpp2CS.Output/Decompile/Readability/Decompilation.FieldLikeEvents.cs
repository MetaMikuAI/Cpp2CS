using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;
using Attribute = ICSharpCode.Decompiler.CSharp.Syntax.Attribute;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 字段式事件的访问器由编译器生成：Delegate.Combine 或 Remove，加上对后备字段的 CompareExchange 循环。
    /// IL2CPP 把 castclass 展开成判断和抛异常，反编译器认不出这个形态，写成带访问器的事件。
    /// 这里按编译器标记和访问器用到的调用认回字段式声明，字段的引用改成事件名；C# 编译器生成的访问器语义相同。
    /// </summary>
    private sealed class FieldLikeEvents : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var declaration in rootNode.Descendants.OfType<CustomEventDeclaration>().ToArray())
            {
                if (declaration.PrivateImplementationType is { } explicitInterface && explicitInterface.ToString().Length > 0) continue;
                if (declaration.Parent is not TypeDeclaration owner || declaration.GetSymbol() is not IEvent symbol) continue;
                if (BackingField(declaration.AddAccessor, "Combine") is not { } field || BackingField(declaration.RemoveAccessor, "Remove") is not { } removed) continue;
                if (!field.Equals(removed) || !field.ReturnType.Equals(symbol.ReturnType)) continue;
                var backing = owner.Members.OfType<FieldDeclaration>().FirstOrDefault(f => f.Variables.Count == 1 && field.Equals((f.Variables.First().GetSymbol() ?? f.GetSymbol()) is IField own ? own.MemberDefinition : null));
                if (backing is null || Shadowed(owner, declaration.Name)) continue;
                // 事件名只在声明它的类型里能当字段用。
                var references = rootNode.Descendants.OfType<Expression>().Where(e => e is MemberReferenceExpression or IdentifierExpression && e.GetSymbol() is IField f && field.Equals(f.MemberDefinition)).ToArray();
                if (references.Any(r => !r.Ancestors.Contains(owner))) continue;
                foreach (var reference in references)
                {
                    if (reference is MemberReferenceExpression member) member.MemberName = declaration.Name;
                    else ((IdentifierExpression)reference).Identifier = declaration.Name;
                }
                var folded = new EventDeclaration { ReturnType = declaration.ReturnType.Clone(), Modifiers = declaration.Modifiers };
                declaration.Attributes.MoveTo(folded.Attributes);
                foreach (var attribute in backing.Attributes.SelectMany(s => s.Attributes))
                    if (!IsGeneratedMarker(attribute)) folded.Attributes.Add(new AttributeSection((Attribute)attribute.Clone()) { AttributeTarget = "field" });
                folded.Variables.Add(new VariableInitializer(declaration.Name));
                folded.CopyAnnotationsFrom(declaration);
                declaration.ReplaceWith(folded);
                backing.Remove();
            }
        }

        private static bool IsGeneratedMarker(Attribute attribute) => attribute.Type.ToString() is var name && (name.Contains("CompilerGenerated") || name.Contains("DebuggerBrowsable"));

        /// <summary>访问器恰好调用 Delegate 的合并方法和一次 CompareExchange，除局部外不写别的位置时，返回交换的字段定义。</summary>
        private static IField? BackingField(Accessor? accessor, string combine)
        {
            if (accessor?.Body is not { } body || !accessor.Attributes.SelectMany(s => s.Attributes).Any(IsGeneratedMarker)) return null;
            var calls = body.Descendants.OfType<InvocationExpression>().ToArray();
            if (calls.Length != 2 || !calls.Any(c => c.GetSymbol() is IMethod { DeclaringType.FullName: "System.Delegate" } m && m.Name == combine)) return null;
            var exchange = calls.FirstOrDefault(c => c.GetSymbol() is IMethod { Name: "CompareExchange", DeclaringType.FullName: "System.Threading.Interlocked" });
            if (body.Descendants.OfType<AssignmentExpression>().Any(a => a.Left.GetSymbol() is IMember)) return null;
            return exchange?.Arguments.FirstOrDefault() is DirectionExpression { Expression: var target } && target.GetSymbol() is IField field ? field.MemberDefinition as IField : null;
        }

        /// <summary>同名的局部或形参会把改名后的字段引用遮住，这样的事件不折叠。</summary>
        private static bool Shadowed(TypeDeclaration owner, string name) =>
            owner.Descendants.Any(n => n is ParameterDeclaration p && p.Name == name || n is VariableInitializer { Parent: VariableDeclarationStatement } v && v.Name == name);
    }
}
