using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.IL;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;
using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;
using PrimitiveType = ICSharpCode.Decompiler.CSharp.Syntax.PrimitiveType;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    private sealed partial class ExpressionForms
    {
        // C# 在泛型约束上调用接口方法时保留接收者的地址。转发实参在原调用处求值。
        private static void ConstrainedInterfaceCall(CastExpression cast)
        {
            if (cast.Parent is not Expression target || !(target is MemberReferenceExpression member && member.Target == cast
                || target is IndexerExpression element && element.Target == cast)) return;
            // 引用返回的属性也可出现在赋值左边；由带调用指令的节点区分取址与 setter。
            Expression site = target.Annotation<CallVirt>() is not null ? target : target.Parent switch
            {
                InvocationExpression call when call.Target == target => call,
                AssignmentExpression assignment when assignment.Left == target => assignment,
                _ => target,
            };
            var instruction = site.Annotations.OfType<CallVirt>().FirstOrDefault(c => c.ConstrainedTo?.Kind == TypeKind.Struct
                && c.Method.DeclaringType.Kind == TypeKind.Interface && c.ConstrainedTo.Equals(cast.Expression.Annotation<ResolveResult>()?.Type));
            if (instruction is null || site.GetParent<BlockStatement>() is not { } block) return;
            var method = instruction.Method;
            var builder = QualifiedTypes;
            var scope = (AstNode?)block.GetParent<EntityDeclaration>() ?? block;
            var names = scope.Descendants.OfType<Identifier>().Select(i => i.Name)
                .Concat(scope.Ancestors.OfType<TypeDeclaration>().SelectMany(t => t.TypeParameters).Select(p => p.Name))
                .Concat(method.Parameters.Select(p => p.Name)).ToHashSet(StringComparer.Ordinal);
            string Fresh(string basis)
            {
                string name = basis;
                for (int i = 1; !names.Add(name); i++) name = basis + i;
                return name;
            }
            var helper = new MethodDeclaration { Name = Fresh("InvokeConstrained"), Modifiers = Modifiers.Static,
                ReturnType = builder.ConvertType(method.ReturnType), Body = new BlockStatement() };
            var typeParameter = Fresh("TReceiver");
            var receiver = Fresh("receiver");
            helper.TypeParameters.Add(new TypeParameterDeclaration { Name = typeParameter });
            helper.Constraints.Add(new Constraint { TypeParameter = new SimpleType(typeParameter),
                BaseTypes = { builder.ConvertType(method.DeclaringType) } });
            // AddressOf 是 ILSpy 的临时值地址；真实存储必须由 ref 贯穿调用。
            bool temporary = instruction.Arguments[0] is AddressOf;
            helper.Parameters.Add(new ParameterDeclaration { Name = receiver, Type = new SimpleType(typeParameter),
                ParameterModifier = temporary ? ReferenceKind.None : ReferenceKind.Ref });
            var actuals = new List<Expression> { temporary ? cast.Expression.Clone()
                : new DirectionExpression(FieldDirection.Ref, cast.Expression.Clone()) };
            if (site is InvocationExpression invoked)
            {
                NamedArgumentOrder(invoked);
                actuals.AddRange(invoked.Arguments.Select(a => a.Clone()));
            }
            else if (target is IndexerExpression indexer) actuals.AddRange(indexer.Arguments.Select(a => a.Clone()));
            if (site is AssignmentExpression store) actuals.Add(store.Right.Clone());
            var forwarded = new List<Expression>();
            foreach (var parameter in method.Parameters)
            {
                var formal = builder.ConvertParameter(parameter);
                var parameterName = string.IsNullOrEmpty(formal.Name) ? Fresh("argument") : formal.Name;
                formal.Name = parameterName;
                helper.Parameters.Add(formal);
                var name = new IdentifierExpression(parameterName);
                forwarded.Add(parameter.ReferenceKind switch
                {
                    ReferenceKind.Ref => new DirectionExpression(FieldDirection.Ref, name),
                    ReferenceKind.Out => new DirectionExpression(FieldDirection.Out, name),
                    ReferenceKind.In or ReferenceKind.RefReadOnly => new DirectionExpression(FieldDirection.In, name),
                    _ => name,
                });
            }
            var body = ForwardInterfaceMember(method, new IdentifierExpression(receiver), forwarded);
            if (method.ReturnType.Kind == TypeKind.Void && site is AssignmentExpression && site.Parent is not ExpressionStatement
                && method.AccessorOwner is IProperty assigned)
                helper.ReturnType = builder.ConvertType(assigned.ReturnType);
            if (method.ReturnTypeIsRefReadOnly && helper.ReturnType is ComposedType reference) reference.HasReadOnlySpecifier = true;
            helper.Body.Statements.Add(helper.ReturnType is PrimitiveType { Keyword: "void" } ? new ExpressionStatement(body)
                : new ReturnStatement(method.ReturnType is ByReferenceType ? new DirectionExpression(FieldDirection.Ref, body) : body));
            site.ReplaceWith(new InvocationExpression(new IdentifierExpression(helper.Name), actuals));
            block.Statements.Add(new LocalFunctionDeclarationStatement { Declaration = helper });
        }

        private static Expression ForwardInterfaceMember(IMethod method, Expression receiver, List<Expression> arguments)
        {
            if (method.AccessorOwner is IProperty property)
            {
                Expression access = property.IsIndexer ? new IndexerExpression(receiver, arguments.Take(property.Parameters.Count))
                    : new MemberReferenceExpression(receiver, property.Name);
                return method.AccessorKind == System.Reflection.MethodSemanticsAttributes.Setter
                    ? new AssignmentExpression(access, arguments[^1]) : access;
            }
            if (method.AccessorOwner is IEvent ev)
            {
                var operation = method.AccessorKind == System.Reflection.MethodSemanticsAttributes.Adder
                    ? AssignmentOperatorType.Add : AssignmentOperatorType.Subtract;
                return new AssignmentExpression(new MemberReferenceExpression(receiver, ev.Name), operation, arguments.Single());
            }
            return new InvocationExpression(new MemberReferenceExpression(receiver, method.Name,
                method.TypeArguments.Select(t => QualifiedTypes.ConvertType(t))), arguments);
        }
    }
}
