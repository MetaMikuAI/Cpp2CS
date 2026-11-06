using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;
using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 反编译器留下的 ctor 调用（base..ctor()、x..ctor(a)）不是合法语法。字段初始化器被内联展开后，基类调用前面是多条语句，
    /// C# 只能让基类构造先运行；这里移到构造函数初始化器，前面的语句留在函数体。基类构造函数若经虚调用读这些字段，
    /// 读到的值会不同，这是 C# 的表达限制。
    /// </summary>
    private sealed class ConstructorCalls : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            // C# 的析构函数自动调用基类的 Finalize，不能显式写（CS0250）。
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().Where(c => c.Target is MemberReferenceExpression { MemberName: "Finalize", Target: BaseReferenceExpression } && c.GetParent<DestructorDeclaration>() is not null).ToArray())
                if (call.Parent is ExpressionStatement finalize) finalize.Remove();
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().Where(c => c.Target is MemberReferenceExpression { MemberName: ".ctor" }).ToArray())
            {
                var target = (MemberReferenceExpression)call.Target;
                if (call.Parent is not ExpressionStatement statement) continue;
                switch (target.Target)
                {
                    case BaseReferenceExpression or ThisReferenceExpression:
                        Chain(call, statement, target.Target is BaseReferenceExpression);
                        break;
                    case IdentifierExpression variable when call.Annotation<ResolveResult>() is InvocationResolveResult { Member: IMethod { DeclaringType: var type } }:
                        statement.Expression = new AssignmentExpression(variable.Clone(), new ObjectCreateExpression(QualifiedTypes.ConvertType(type), call.Arguments.Select(a => a.Clone())));
                        break;
                    case CastExpression { Expression: NullReferenceExpression } when !call.Arguments.Any():
                        // 接收者未恢复的 object 构造函数调用，没有效果。
                        statement.Remove();
                        break;
                }
            }
        }

        private static void Chain(InvocationExpression call, ExpressionStatement statement, bool toBase)
        {
            if (statement.Parent is not BlockStatement { Parent: ConstructorDeclaration constructor } body)
            {
                // 分支里的无参基类调用：隐式的 base() 已经先运行。object 的构造函数在任何位置都没有效果。
                var isObject = call.Annotation<ResolveResult>() is InvocationResolveResult { Member: var member } && member.DeclaringType.IsKnownType(KnownTypeCode.Object);
                if (toBase && !call.Arguments.Any() && (statement.GetParent<ConstructorDeclaration>() is not null || isObject)) statement.Remove();
                return;
            }
            var arguments = call.Arguments.Select(a => a.Clone()).ToArray();
            if (!InlinePrologue(body, statement, arguments)) return;
            statement.Remove();
            if (arguments.Length == 0 && toBase) return;
            var initializer = new ConstructorInitializer { ConstructorInitializerType = toBase ? ConstructorInitializerType.Base : ConstructorInitializerType.This };
            initializer.Arguments.AddRange(arguments);
            constructor.Initializer = initializer;
        }

        /// <summary>
        /// 构造函数初始化器只能写表达式。实参用到前面的局部时，把定义它们的语句（赋值、两路分支、判空）求值成表达式代回实参；
        /// 判空由随后的成员访问抛出同样的异常。求不出来或会重复求值有副作用的表达式时不改写。
        /// </summary>
        private static bool InlinePrologue(BlockStatement body, ExpressionStatement call, Expression[] arguments)
        {
            var prologue = body.Statements.TakeWhile(s => s != call).ToArray();
            var locals = prologue.OfType<VariableDeclarationStatement>().SelectMany(d => d.Variables).Select(v => v.Name).ToHashSet();
            bool Mentions(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(i => locals.Contains(i.Identifier));
            if (!arguments.Any(Mentions)) return true;
            if (body.Statements.SkipWhile(s => s != call).Skip(1).Any(Mentions)) return false;
            var values = new Dictionary<string, Expression?>();
            var consumed = prologue.Where(s => s is VariableDeclarationStatement || Mentions(s)).ToArray();
            if (!consumed.All(s => Evaluate(s, values, locals))) return false;
            for (var i = 0; i < arguments.Length; i++)
            {
                if (Substitute(arguments[i], values) is not { } value) return false;
                arguments[i] = value;
            }
            var effects = arguments.SelectMany(a => a.DescendantsAndSelf).Where(n => n is InvocationExpression or ObjectCreateExpression).Select(n => n.ToString()).ToArray();
            if (effects.Length != effects.Distinct().Count()) return false;
            foreach (var statement in consumed) statement.Remove();
            return true;
        }

        private static bool Evaluate(Statement statement, Dictionary<string, Expression?> values, HashSet<string> locals)
        {
            switch (statement)
            {
                case VariableDeclarationStatement declaration:
                    foreach (var variable in declaration.Variables)
                    {
                        if (variable.Initializer is null) values[variable.Name] = null;
                        else if (Substitute(variable.Initializer, values) is { } value) values[variable.Name] = value;
                        else return false;
                    }
                    return true;
                case ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression target, Right: var right } } when locals.Contains(target.Identifier):
                    return (values[target.Identifier] = Substitute(right, values)) is not null;
                case BlockStatement block:
                    return block.Statements.All(s => Evaluate(s, values, locals));
                case IfElseStatement { TrueStatement: BlockStatement { Statements: { Count: 1 } only }, FalseStatement: null } when only.First() is ThrowStatement:
                    return true;
                case IfElseStatement conditional when Substitute(conditional.Condition, values) is { } condition:
                {
                    var whenTrue = new Dictionary<string, Expression?>(values);
                    var whenFalse = new Dictionary<string, Expression?>(values);
                    if (!Evaluate(conditional.TrueStatement, whenTrue, locals)) return false;
                    if (conditional.FalseStatement is not null && !Evaluate(conditional.FalseStatement, whenFalse, locals)) return false;
                    foreach (var name in whenTrue.Keys.ToArray())
                    {
                        whenFalse.TryGetValue(name, out var otherwise);
                        if (ReferenceEquals(whenTrue[name], otherwise)) continue;
                        values[name] = whenTrue[name] is { } yes && otherwise is { } no ? new ConditionalExpression(condition.Clone(), yes.Clone(), no.Clone()) : null;
                    }
                    return true;
                }
                default:
                    return false;
            }
        }

        private static Expression? Substitute(Expression expression, Dictionary<string, Expression?> values)
        {
            var result = expression.Clone();
            foreach (var identifier in result.DescendantsAndSelf.OfType<IdentifierExpression>().ToArray())
            {
                if (!values.TryGetValue(identifier.Identifier, out var value)) continue;
                if (value is null) return null;
                if (identifier == result) return value.Clone();
                identifier.ReplaceWith(value.Clone());
            }
            return result;
        }
    }

    /// <summary>
    /// 结构体构造函数在 C# 9 必须给全部字段赋值（CS0171、CS0188）。this = new T { ... } 在只读字段上不合法，拆成逐字段赋值；
    /// 字段没写全时先 this = default。CIL 里没写的字段是调用方的内容，这是 C# 的表达限制。
    /// </summary>
    private sealed class StructConstructors : IAstTransform
    {
        /// <summary>嵌套的成员初始化器 A = { x = 1 } 展开成 A.x = 1。</summary>
        private static IEnumerable<Statement> Assignments(Expression target, Expression value)
        {
            if (value is not ArrayInitializerExpression nested)
            {
                yield return new ExpressionStatement(new AssignmentExpression(target, value.Clone()));
                yield break;
            }
            foreach (var element in nested.Elements.OfType<NamedExpression>())
                foreach (var assignment in Assignments(new MemberReferenceExpression(target.Clone(), element.Name), element.Expression))
                    yield return assignment;
        }

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var constructor in rootNode.Descendants.OfType<ConstructorDeclaration>())
            {
                if (constructor.Parent is not TypeDeclaration { ClassType: ClassType.Struct } type || constructor.HasModifier(Modifiers.Static) || constructor.Body is null) continue;
                if (constructor.Initializer is { ConstructorInitializerType: ConstructorInitializerType.This }) continue;
                foreach (var statement in constructor.Body.Statements.ToArray())
                {
                    if (statement is not ExpressionStatement { Expression: AssignmentExpression { Left: ThisReferenceExpression, Right: ObjectCreateExpression { Arguments.Count: 0, Initializer: { } initializer } } }) continue;
                    var anchor = statement;
                    foreach (var element in initializer.Elements.OfType<NamedExpression>())
                    {
                        foreach (var assignment in Assignments(new MemberReferenceExpression(new ThisReferenceExpression(), element.Name), element.Expression))
                        {
                            constructor.Body.Statements.InsertAfter(anchor, assignment);
                            anchor = assignment;
                        }
                    }
                    statement.Remove();
                }
                var assigned = constructor.Body.Statements.OfType<ExpressionStatement>().Select(s => s.Expression).OfType<AssignmentExpression>()
                    .Where(a => a.Operator == AssignmentOperatorType.Assign).Select(a => a.Left switch
                    {
                        IdentifierExpression i => i.Identifier,
                        MemberReferenceExpression { Target: ThisReferenceExpression } m => m.MemberName,
                        _ => null,
                    }).ToHashSet();
                if (constructor.Body.Statements.OfType<ExpressionStatement>().Any(s => s.Expression is AssignmentExpression { Left: ThisReferenceExpression })) continue;
                var fields = type.Members.OfType<FieldDeclaration>().Where(f => !f.HasModifier(Modifiers.Static) && !f.HasModifier(Modifiers.Const)).SelectMany(f => f.Variables).Select(v => v.Name)
                    .Concat(type.Members.OfType<PropertyDeclaration>().Where(p => !p.HasModifier(Modifiers.Static) && p.Getter is { Body: null }).Select(p => p.Name));
                if (fields.All(assigned.Contains)) continue;
                constructor.Body.Statements.InsertBefore(constructor.Body.Statements.FirstOrDefault(), new ExpressionStatement(new AssignmentExpression(new ThisReferenceExpression(), new DefaultValueExpression(null!))));
            }
        }
    }
}
