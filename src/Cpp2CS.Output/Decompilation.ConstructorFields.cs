using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>唯一构造函数中基类调用之前的字段写入，按求值顺序还原成字段初始化器。</summary>
    private sealed class ConstructorFields : IAstTransform
    {
        private sealed record Initializer(FieldDeclaration Field, Expression Value, int[] Positions, bool Constant);

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var type in rootNode.Descendants.OfType<TypeDeclaration>()) Lift(type);
        }

        private static void Lift(TypeDeclaration type)
        {
            if (type.ClassType != ClassType.Class || type.Attributes.SelectMany(a => a.Attributes).Any(a => a.Type.ToString().Contains("StructLayout"))
                || type.Members.OfType<ConstructorDeclaration>().Where(c => !c.Modifiers.HasFlag(Modifiers.Static)).ToArray() is not [var ctor]
                || ctor.Parameters.Count != 0 || ctor.Initializer is not null || ctor.Body is not { } body
                || body.Statements.LastOrDefault() is not ExpressionStatement { Expression: InvocationExpression
                    { Target: MemberReferenceExpression { Target: BaseReferenceExpression, MemberName: "_002Ector" }, Arguments.Count: 0 } } baseCall) return;
            var fields = type.Members.OfType<FieldDeclaration>().Where(f => (f.Modifiers & (Modifiers.Static | Modifiers.Const)) == 0).ToArray();
            if (fields.Any(f => f.Variables.Count != 1 || f.Variables.Single().Initializer is not null)) return;
            var byName = fields.ToDictionary(f => f.Variables.Single().Name);
            var statements = body.Statements.Take(body.Statements.Count - 1).ToArray();
            var locals = new Dictionary<string, (Expression Value, int Position)>();
            var writes = new Dictionary<string, List<(string? Component, Expression Value, int Position)>>();
            for (var i = 0; i < statements.Length; i++)
            {
                if (statements[i] is VariableDeclarationStatement declaration && declaration.Variables.ToArray() is [var local])
                {
                    if (local.Initializer is null || !locals.TryAdd(local.Name, (local.Initializer, i))) return;
                    continue;
                }
                if (statements[i] is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign } assignment }) return;
                string? Name(Expression e) => e switch
                {
                    IdentifierExpression id => id.Identifier,
                    MemberReferenceExpression { Target: ThisReferenceExpression } member => member.MemberName,
                    _ => null,
                };
                var name = Name(assignment.Left);
                string? component = null;
                if (name is null && assignment.Left is MemberReferenceExpression member)
                {
                    name = Name(member.Target);
                    component = member.MemberName;
                }
                if (name is null || !byName.ContainsKey(name)) return;
                if (!writes.TryGetValue(name, out var values)) writes.Add(name, values = []);
                values.Add((component, assignment.Right, i));
            }
            var used = new HashSet<string>();
            var initializers = new List<Initializer>();
            foreach (var (name, writesToField) in writes)
            {
                var positions = writesToField.Select(w => w.Position).ToList();
                Expression? Expand(Expression value, int usePosition)
                {
                    if (value.DescendantsAndSelf.Any(n => n is ThisReferenceExpression or BaseReferenceExpression)) return null;
                    var copy = value.Clone();
                    foreach (var identifier in copy.DescendantsAndSelf.OfType<IdentifierExpression>().ToArray())
                    {
                        if (byName.ContainsKey(identifier.Identifier)) return null;
                        if (!locals.TryGetValue(identifier.Identifier, out var source)) continue;
                        if (!used.Add(identifier.Identifier) || source.Position >= usePosition) return null;
                        positions.Add(source.Position);
                        var replacement = Expand(source.Value, source.Position);
                        if (replacement is null) return null;
                        if (ReferenceEquals(copy, identifier)) copy = replacement;
                        else identifier.ReplaceWith(replacement);
                    }
                    return copy;
                }
                var expressions = writesToField.Select(w => Expand(w.Value, w.Position)).ToArray();
                if (expressions.Any(e => e is null)) return;
                var field = byName[name];
                Expression expression;
                if (writesToField.Count == 1 && writesToField[0].Component is null) expression = expressions[0]!;
                else
                {
                    if (writesToField.Any(w => w.Component is null) || writesToField.Select(w => w.Component).Distinct().Count() != writesToField.Count
                        || (field.Variables.Single().GetSymbol() ?? field.GetSymbol()) is not IField { Type.IsReferenceType: false } symbol
                        || symbol.Type.GetDefinition() is not { } structure
                        || structure.Methods.Any(m => m.IsConstructor && !m.IsStatic && m.Parameters.Count == 0 && !m.MetadataToken.IsNil)
                        || structure.Fields.Any(f => !f.IsStatic && (f.Accessibility != Accessibility.Public || f.IsReadOnly))
                        || structure.Fields.Where(f => !f.IsStatic).Select(f => f.Name).Except(writesToField.Select(w => w.Component!)).Any()) return;
                    var initializer = new ArrayInitializerExpression();
                    for (var i = 0; i < writesToField.Count; i++) initializer.Elements.Add(new NamedExpression(writesToField[i].Component!, expressions[i]!));
                    expression = new ObjectCreateExpression(field.ReturnType.Clone()) { Initializer = initializer };
                }
                var constant = expressions.All(e => e is PrimitiveExpression or NullReferenceExpression or DefaultValueExpression);
                initializers.Add(new(field, expression, positions.ToArray(), constant));
            }
            if (used.Count != locals.Count) return;
            // 交错的结构体叶子只能跨过无副作用的常量字段写入，不能改变工厂调用等求值顺序。
            foreach (var a in initializers)
                foreach (var b in initializers)
                    if (a != b && a.Positions.Min() < b.Positions.Min() && a.Positions.Max() > b.Positions.Min() && !b.Constant) return;
            var anchor = type.Members.FirstOrDefault(m => !initializers.Any(i => ReferenceEquals(m, i.Field)));
            foreach (var initializer in initializers.OrderBy(i => i.Positions.Min()))
            {
                var field = initializer.Field;
                field.Remove();
                field.Variables.Single().Initializer = initializer.Value;
                type.Members.InsertBefore(anchor, field);
            }
            foreach (var statement in statements) statement.Remove();
            baseCall.Remove();
            ctor.Initializer = new ConstructorInitializer { ConstructorInitializerType = ConstructorInitializerType.Base };
        }
    }
}
