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
                    case not null when !call.Arguments.Any() && call.Annotation<ResolveResult>() is InvocationResolveResult { Member.DeclaringType: var owner } && owner.IsKnownType(KnownTypeCode.Object):
                        // object 的构造函数没有效果；对别的对象调用时写成 new object() 会换掉对象，直接去掉。
                        statement.Remove();
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
        /// 构造函数初始化器只能写表达式。实参用到前面的局部时，把定义它们的语句（赋值、两路分支、判空、新数组的逐元素写入）求值成表达式代回实参；
        /// 判空由随后的成员访问抛出同样的异常。求不出来或会重复求值有副作用的表达式时不改写。
        /// 调用之后还用到的局部，值是常量或函数体里没有被写过的形参时，同样代回；求值结果和基类构造之前相同。
        /// </summary>
        private static bool InlinePrologue(BlockStatement body, ExpressionStatement call, Expression[] arguments)
        {
            var prologue = body.Statements.TakeWhile(s => s != call).ToArray();
            var locals = prologue.OfType<VariableDeclarationStatement>().SelectMany(d => d.Variables).Select(v => v.Name).ToHashSet();
            bool Mentions(AstNode node) => node.DescendantsAndSelf.OfType<IdentifierExpression>().Any(i => locals.Contains(i.Identifier));
            if (!arguments.Any(Mentions)) return true;
            var later = body.Statements.SkipWhile(s => s != call).Skip(1).ToArray();
            var reused = locals.Where(l => later.Any(s => s.DescendantsAndSelf.OfType<IdentifierExpression>().Any(i => i.Identifier == l))).ToArray();
            var values = new Dictionary<string, Expression?>();
            var consumed = prologue.Where(s => s is VariableDeclarationStatement || Mentions(s)).ToArray();
            if (!consumed.All(s => Evaluate(s, values, locals))) return false;
            var parameters = body.GetParent<ConstructorDeclaration>()!.Parameters.Select(p => p.Name).ToHashSet();
            bool Stable(Expression value) => value is PrimitiveExpression or NullReferenceExpression
                || value is IdentifierExpression parameter && parameters.Contains(parameter.Identifier) && !Writes(body, parameter.Identifier);
            if (reused.Any(name => values.GetValueOrDefault(name) is not { } value || !Stable(value) || later.Any(s => Writes(s, name)))) return false;
            for (var i = 0; i < arguments.Length; i++)
            {
                if (Substitute(arguments[i], values) is not { } value) return false;
                arguments[i] = value;
            }
            // 模式声明的变量只在留在函数体里的判断中定义，代回初始化器后就不在作用域内。
            var patterns = prologue.SelectMany(s => s.Descendants.OfType<SingleVariableDesignation>()).Select(d => d.Identifier).ToHashSet();
            if (arguments.Any(a => a.DescendantsAndSelf.OfType<IdentifierExpression>().Any(i => patterns.Contains(i.Identifier)))) return false;
            var effects = arguments.SelectMany(a => a.DescendantsAndSelf).Where(n => n is InvocationExpression or ObjectCreateExpression or ArrayCreateExpression).Select(n => n.ToString()).ToArray();
            if (effects.Length != effects.Distinct().Count()) return false;
            foreach (var statement in consumed) statement.Remove();
            foreach (var identifier in later.SelectMany(s => s.DescendantsAndSelf.OfType<IdentifierExpression>()).Where(i => reused.Contains(i.Identifier)).ToArray())
                identifier.ReplaceWith(values[identifier.Identifier]!.Clone());
            return true;
        }

        /// <summary>局部或形参在节点内被赋值、自增减或按引用传出。</summary>
        private static bool Writes(AstNode node, string name)
        {
            static bool Is(Expression e, string name) => e is IdentifierExpression identifier && identifier.Identifier == name;
            return node.DescendantsAndSelf.Any(n => n switch
            {
                AssignmentExpression assignment => Is(assignment.Left, name),
                UnaryOperatorExpression { Operator: UnaryOperatorType.Increment or UnaryOperatorType.Decrement or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf } unary => Is(unary.Expression, name),
                DirectionExpression direction => Is(direction.Expression, name),
                _ => false,
            });
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
                case ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IndexerExpression { Target: IdentifierExpression array, Arguments.Count: 1 } element, Right: var right } }
                    when locals.Contains(array.Identifier) && values.GetValueOrDefault(array.Identifier) is ArrayCreateExpression creation:
                    return (values[array.Identifier] = Store(creation, element.Arguments.Single(), Substitute(right, values))) is not null;
                case BlockStatement block:
                    return block.Statements.All(s => Evaluate(s, values, locals));
                case IfElseStatement { TrueStatement: BlockStatement { Statements: { Count: 1 } only }, FalseStatement: null } conditional when only.First() is ThrowStatement:
                    // 条件里的模式声明的变量在后面还会用到，删掉判断就没有定义了。
                    return !conditional.Condition.DescendantsAndSelf.OfType<SingleVariableDesignation>().Any();
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

        /// <summary>
        /// 定长的新数组按下标递增逐个写入元素，写成数组初始化器；没写到的元素是 default，新数组本来就是零，写成 null 或 default 的元素也是零。
        /// 元素按下标顺序求值，和逐条写入的次序相同。
        /// </summary>
        private static ArrayCreateExpression? Store(ArrayCreateExpression creation, Expression index, Expression? value)
        {
            if (value is null || creation.Type is not { } elementType || creation.Arguments.Count != 1 || creation.AdditionalArraySpecifiers.Count != 0
                || creation.Arguments.Single() is not PrimitiveExpression { Value: int length } || index is not PrimitiveExpression { Value: int at } || at < 0 || at >= length)
                return null;
            var next = (ArrayCreateExpression)creation.Clone();
            if (next.Initializer is not { Elements.Count: > 0 } initializer)
            {
                initializer = new ArrayInitializerExpression();
                for (var i = 0; i < length; i++) initializer.Elements.Add(new DefaultValueExpression(elementType.Clone()));
                next.Initializer = initializer;
            }
            if (initializer.Elements.Count != length) return null;
            var elements = initializer.Elements.ToArray();
            // 已写过的元素都在前面：写入次序就是初始化器的求值次序。反编译器只认出前几个元素时，其余写成 null。
            if (elements.Skip(at).Any(e => e is not (DefaultValueExpression or NullReferenceExpression))) return null;
            elements[at].ReplaceWith(value.Clone());
            return next;
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
    /// C# 按文字顺序执行字段初始化器，反编译器却把字段排在属性前面：后备字段在元数据里靠前的自动属性，初始化得比原来晚。
    /// Roslyn 按声明顺序写出字段，元数据的顺序就是原来的文字顺序。初始化器的先后不对时，把声明挪到元数据顺序的位置。
    /// </summary>
    private sealed class InitializerOrder : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var type in rootNode.Descendants.OfType<TypeDeclaration>().ToArray())
            {
                if (type.Annotation<TypeResolveResult>()?.Type.GetDefinition() is not { } definition) continue;
                var fields = definition.Fields.ToArray();
                var initialized = new List<(EntityDeclaration Member, int Index, bool Static)>();
                foreach (var member in type.Members)
                {
                    var name = member switch
                    {
                        FieldDeclaration field when field.Variables.Count == 1 && field.Variables.Single().Initializer is not null => field.Variables.Single().Name,
                        PropertyDeclaration property when property.Initializer is not null => $"<{property.Name}>k__BackingField",
                        _ => null,
                    };
                    var index = name is null ? -1 : Array.FindIndex(fields, f => f.Name == name);
                    if (index >= 0) initialized.Add((member, index, member.HasModifier(Modifiers.Static)));
                }
                foreach (var group in initialized.GroupBy(i => i.Static))
                {
                    EntityDeclaration? last = null;
                    foreach (var (member, _, _) in group.OrderBy(i => i.Index))
                    {
                        if (last is not null && type.Members.TakeWhile(m => m != last).Contains(member))
                        {
                            member.Remove();
                            type.Members.InsertAfter(last, member);
                        }
                        last = member;
                    }
                }
            }
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
