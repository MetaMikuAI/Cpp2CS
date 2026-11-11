using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 内联把公开方法的实现展开到调用方，留下运行时和引擎的私有成员。它们只有放宽后的引用才能绑定，真实引用上编译不过：
    /// 折回对应的公开写法。私有的抛异常方法没有公开入口，写成同类型的异常，消息文本不保留。
    /// </summary>
    private sealed class LibraryInternals : IAstTransform
    {
        private const double Degrees = Math.PI / 180;

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().Reverse().ToArray())
            {
                if (call.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod method }) continue;
                switch (method.DeclaringTypeDefinition?.FullName, method.Name)
                {
                    case ("System.String", "CreateString"):
                        call.ReplaceWith(new ObjectCreateExpression(new PrimitiveType("string"), call.Arguments.Select(a => a.Clone())));
                        break;
                    case ("System.String", "GetRawStringData"):
                        UnusedReference(call);
                        break;
                    case ("System.Math", "ThrowAbsOverflow"):
                        Throw(call, "OverflowException");
                        break;
                    case ("System.Math", "ThrowMinMaxException"):
                        Throw(call, "ArgumentException");
                        break;
                    case ("System.Collections.Generic.HashSet", "AddIfNotPresent") when call.Target is MemberReferenceExpression target:
                        target.MemberName = "Add";
                        break;
                    case ("UnityEngine.Quaternion", "Internal_FromEulerRad"):
                        FromEuler(call);
                        break;
                    case ("UnityEngine.Quaternion", "Internal_ToEulerRad"):
                        ToEuler(call);
                        break;
                }
            }
            foreach (var creation in rootNode.Descendants.OfType<ObjectCreateExpression>().Reverse().ToArray())
            {
                NestedEnumerator(creation);
                InlinedConstructor(creation);
                SpanFromReference(creation);
            }
            foreach (var block in rootNode.Descendants.OfType<BlockStatement>().ToArray()) ReadOnlyFieldRuns(block);
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().ToArray()) ComparerImplementation(cast);
        }

        private static void Throw(InvocationExpression call, string exception)
        {
            if (call.Parent is ExpressionStatement statement) statement.ReplaceWith(new ThrowStatement(new ObjectCreateExpression(GlobalType("System", exception))));
        }

        /// <summary>string.AsSpan 展开后只取地址和长度，取到的地址没有用到时直接去掉。</summary>
        private static void UnusedReference(InvocationExpression call)
        {
            if (call.Parent is not DirectionExpression { Parent: VariableInitializer { Parent: VariableDeclarationStatement declaration } variable }) return;
            var function = EnclosingFunction(declaration)!;
            if (!function.Descendants.OfType<IdentifierExpression>().Any(i => i.Identifier == variable.Name)) declaration.Remove();
        }

        /// <summary>
        /// Quaternion.Euler 展开成 Internal_FromEulerRad(new Vector3(x, y, z) * Deg2Rad)，常量已折叠成弧度。
        /// 形状不完整时用 Euler(v * Rad2Deg)：Euler 内部再乘回去，只差浮点舍入。
        /// </summary>
        private static void FromEuler(InvocationExpression call)
        {
            if (call.Target is not MemberReferenceExpression { Target: var owner } || call.Arguments.FirstOrDefault() is not { } argument) return;
            var euler = new MemberReferenceExpression(owner.Clone(), "Euler");
            if (argument is DefaultValueExpression)
                call.ReplaceWith(new InvocationExpression(euler, argument.Clone()));
            else if (Components(argument, Degrees, missingIsZero: true) is { } components)
                call.ReplaceWith(new InvocationExpression(euler, components.Select(c => c.Clone())));
            else if (argument is BinaryOperatorExpression { Operator: BinaryOperatorType.Multiply, Left: var vector, Right: var factor } && IsConstant(factor, Degrees))
                call.ReplaceWith(new InvocationExpression(euler, vector!.Clone()));
            else
                call.ReplaceWith(new InvocationExpression(euler, new BinaryOperatorExpression(argument.Clone(), BinaryOperatorType.Multiply, new PrimitiveExpression((float)(1 / Degrees)))));
        }

        /// <summary>
        /// eulerAngles 展开成 v = Internal_ToEulerRad(q)、Internal_MakePositive(v * Rad2Deg)。
        /// v 只在这里用到时折回：先取 eulerAngles，原来取正的位置读这个结果。
        /// </summary>
        private static void ToEuler(InvocationExpression call)
        {
            if (call.Parent is not VariableInitializer { Parent: VariableDeclarationStatement declaration } variable || call.Arguments.FirstOrDefault() is not { } quaternion) return;
            var function = EnclosingFunction(declaration)!;
            var uses = function.Descendants.OfType<IdentifierExpression>().Where(i => i.Identifier == variable.Name).ToArray();
            if (uses.Length != 3 || !uses.All(u => u.Parent is MemberReferenceExpression { Parent: BinaryOperatorExpression { Parent: NamedExpression { Parent: ArrayInitializerExpression { Parent: ObjectCreateExpression { Parent: InvocationExpression } } } } })) return;
            var positive = (InvocationExpression)uses[0].Ancestors.OfType<ObjectCreateExpression>().First().Parent!;
            if (positive.Target is not MemberReferenceExpression { MemberName: "Internal_MakePositive" } || positive.Arguments.FirstOrDefault() is not { } argument) return;
            if (Components(argument, 1 / Degrees, missingIsZero: false) is not { } components) return;
            string[] axes = ["x", "y", "z"];
            if (!components.Select((c, i) => c is MemberReferenceExpression { Target: IdentifierExpression source } member && source.Identifier == variable.Name && member.MemberName == axes[i]).All(b => b)) return;
            positive.ReplaceWith(new IdentifierExpression(variable.Name));
            call.ReplaceWith(new MemberReferenceExpression(quaternion.Clone(), "eulerAngles"));
        }

        /// <summary>new Vector3 { x = a * k, y = b * k, z = c * k } 里的 a、b、c；不是这个形状时返回 null。</summary>
        private static Expression[]? Components(Expression vector, double factor, bool missingIsZero)
        {
            if (vector is not ObjectCreateExpression { Initializer: { } initializer }) return null;
            var elements = initializer.Elements.OfType<NamedExpression>().ToDictionary(e => e.Name, e => e.Expression);
            string[] axes = ["x", "y", "z"];
            var result = new Expression[3];
            for (var i = 0; i < 3; i++)
            {
                if (!elements.TryGetValue(axes[i], out var element))
                {
                    if (!missingIsZero) return null;
                    result[i] = new PrimitiveExpression(0f);
                    continue;
                }
                if (missingIsZero && Constant(element) is { } folded)
                {
                    result[i] = new PrimitiveExpression((float)Math.Round(folded / factor, 3));
                    continue;
                }
                if (element is not BinaryOperatorExpression { Operator: BinaryOperatorType.Multiply } product) return null;
                if (IsConstant(product.Right, factor)) result[i] = product.Left!;
                else if (IsConstant(product.Left, factor)) result[i] = product.Right!;
                else return null;
            }
            return result;
        }

        private static bool IsConstant(Expression? expression, double expected) =>
            Constant(expression) is { } value && Math.Abs(value - expected) <= Math.Abs(expected) * 1e-6;

        private static double? Constant(Expression? expression) => expression switch
        {
            PrimitiveExpression { Value: float value } => value,
            PrimitiveExpression { Value: double value } => value,
            CastExpression { Expression: var inner } => Constant(inner),
            UnaryOperatorExpression { Operator: UnaryOperatorType.Minus, Expression: var inner } when Constant(inner) is { } a => -a,
            BinaryOperatorExpression { Operator: BinaryOperatorType.Divide, Left: var left, Right: var right } when Constant(left) is { } a && Constant(right) is { } b => a / b,
            BinaryOperatorExpression { Operator: BinaryOperatorType.Multiply, Left: var left, Right: var right } when Constant(left) is { } a && Constant(right) is { } b => a * b,
            MemberReferenceExpression { MemberName: "PI" } => Math.PI,
            _ => null,
        };

        /// <summary>集合的枚举器构造函数不公开：new List&lt;T&gt;.Enumerator(list) 是 GetEnumerator 展开后的形状。</summary>
        private static void NestedEnumerator(ObjectCreateExpression creation)
        {
            if (creation.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod { IsConstructor: true, DeclaringTypeDefinition: { Name: "Enumerator", DeclaringTypeDefinition: { } collection } } }) return;
            if (creation.Arguments.Count != 1 || creation.Arguments.First().Annotation<ResolveResult>()?.Type.GetDefinition() is not { } source || !source.Equals(collection)) return;
            creation.ReplaceWith(new InvocationExpression(new MemberReferenceExpression(creation.Arguments.First().Clone(), "GetEnumerator")));
        }

        /// <summary>
        /// Span 和 ReadOnlySpan 按引用构造的构造函数不公开，是 string.AsSpan、栈上缓冲区之类展开后的形状：
        /// new ReadOnlySpan&lt;char&gt;(ref s.GetRawStringData(), s.Length) 写成 MemoryExtensions.AsSpan(s, 0, s.Length)，
        /// s 为 null 时同样在取长度处抛空引用异常；new Span&lt;T&gt;(ref *p, n) 写成指针构造函数 new Span&lt;T&gt;(p, n)，
        /// 公开的构造函数多检查一次 n 不为负（不检查的构造函数要求调用方保证）。
        /// </summary>
        private static void SpanFromReference(ObjectCreateExpression creation)
        {
            if (creation.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod { IsConstructor: true, DeclaringTypeDefinition: { Namespace: "System", Name: "Span" or "ReadOnlySpan" } span } constructor }
                || constructor.Parameters.Count != 2 || constructor.Parameters[0].Type.Kind != ICSharpCode.Decompiler.TypeSystem.TypeKind.ByReference
                || creation.Arguments.ToArray() is not [DirectionExpression { FieldDirection: FieldDirection.Ref, Expression: var reference }, var length]) return;
            if (span.Name == "ReadOnlySpan" && reference is InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetRawStringData", Target: { } text } } raw
                && raw.Annotation<ResolveResult>() is InvocationResolveResult { Member.DeclaringTypeDefinition.KnownTypeCode: KnownTypeCode.String }
                && length is MemberReferenceExpression { MemberName: "Length", Target: { } measured } && measured.ToString() == text.ToString()
                && !text.DescendantsAndSelf.Any(n => n is InvocationExpression or AssignmentExpression or UnaryOperatorExpression { Operator: UnaryOperatorType.Await or UnaryOperatorType.Increment or UnaryOperatorType.Decrement or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement }))
            {
                var asSpan = new MemberReferenceExpression(new TypeReferenceExpression(GlobalType("System", "MemoryExtensions")), "AsSpan");
                creation.ReplaceWith(new InvocationExpression(asSpan, text.Clone(), new PrimitiveExpression(0), length.Clone()));
                return;
            }
            if (reference is UnaryOperatorExpression { Operator: UnaryOperatorType.Dereference, Expression: var pointer })
                creation.ReplaceWith(new ObjectCreateExpression(creation.Type.Clone(), pointer.Clone(), length.Clone()));
        }

        /// <summary>
        /// 外部类型的构造函数展开成给只读字段赋值的初始化器，源码写不出来。换回形参类型按顺序对得上字段的构造函数；
        /// 不是形参的字段由构造函数自己算出，它们的值表达式必须没有副作用。
        /// </summary>
        private static void InlinedConstructor(ObjectCreateExpression creation)
        {
            if (creation.Initializer is not { } initializer || creation.Arguments.Count != 0) return;
            if ((creation.Annotation<ResolveResult>()?.Type ?? creation.Type.Annotation<ResolveResult>()?.Type)?.GetDefinition() is not { } type || type.ParentModule?.IsMainModule != false) return;
            var elements = initializer.Elements.OfType<NamedExpression>().ToArray();
            if (elements.Length == 0 || elements.Length != initializer.Elements.Count) return;
            var fields = elements.Select(e => type.Fields.FirstOrDefault(f => f.Name == e.Name)).ToArray();
            if (fields.Any(f => f is null || !f.IsReadOnly)) return;
            if (Construct(creation.Type.Clone(), type, fields!, elements.Select(e => e.Expression!).ToArray()) is { } constructed) creation.ReplaceWith(constructed);
        }

        /// <summary>结构体复制按字段展开成连续的写入，同样写不出来：覆盖全部实例字段时换回构造函数。</summary>
        private static void ReadOnlyFieldRuns(BlockStatement block)
        {
            var statements = block.Statements.ToArray();
            for (var i = 0; i < statements.Length; i++)
            {
                if (ReadOnlyWrite(statements[i]) is not { } first) continue;
                var run = statements.Skip(i).Select(ReadOnlyWrite).TakeWhile(w => w is not null && w.Value.Target.ToString() == first.Target.ToString()).Select(w => w!.Value).ToArray();
                var type = first.Field.DeclaringTypeDefinition!;
                if (run.Length == type.Fields.Count(f => !f.IsStatic)
                    && Construct(QualifiedTypes.ConvertType(type), type, run.Select(w => w.Field).ToArray(), run.Select(w => w.Value).ToArray()) is { } constructed)
                {
                    statements[i].ReplaceWith(new ExpressionStatement(new AssignmentExpression(first.Target.Clone(), constructed)));
                    foreach (var statement in statements.Skip(i + 1).Take(run.Length - 1)) statement.Remove();
                }
                i += run.Length - 1;
            }
        }

        private static (Expression Target, IField Field, Expression Value)? ReadOnlyWrite(Statement statement) =>
            statement is ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: MemberReferenceExpression { Target: { } target } member, Right: { } value } }
            && member.Annotation<MemberResolveResult>()?.Member is IField { IsReadOnly: true, IsStatic: false, ParentModule.IsMainModule: false } field
                ? (target, field, value)
                : null;

        private static ObjectCreateExpression? Construct(AstType type, ITypeDefinition definition, IField[] fields, Expression[] values)
        {
            var chosen = definition.Methods.Where(m => m.IsConstructor && !m.IsStatic && m.Parameters.Count > 0)
                .Select(m => (Method: m, Positions: Positions(m, fields)))
                .Where(c => c.Positions is not null).OrderByDescending(c => c.Method.Parameters.Count).ThenBy(c => string.Join(",", c.Positions!)).FirstOrDefault();
            if (chosen.Positions is not { } positions) return null;
            if (values.Where((_, i) => !positions.Contains(i)).Any(e => e.DescendantsAndSelf.Any(n => n is InvocationExpression or AssignmentExpression or UnaryOperatorExpression { Operator: UnaryOperatorType.Await }))) return null;
            return new ObjectCreateExpression(type, positions.Select(i => values[i].Clone()));
        }

        /// <summary>形参依次对应的字段位置（类型相同、顺序一致）；对不上时返回 null。</summary>
        private static int[]? Positions(IMethod constructor, IField[] fields)
        {
            var result = new List<int>();
            var next = 0;
            foreach (var parameter in constructor.Parameters)
            {
                while (next < fields.Length && !fields[next].ReturnType.Equals(parameter.Type)) next++;
                if (next == fields.Length) return null;
                result.Add(next++);
            }
            return result.ToArray();
        }

        /// <summary>StringComparer 的属性展开后转换成内部实现类；实现类不公开，用基类的值即可。</summary>
        private static void ComparerImplementation(CastExpression cast)
        {
            if ((cast.Annotation<ResolveResult>()?.Type ?? cast.Type.Annotation<ResolveResult>()?.Type)?.GetDefinition() is not { } target) return;
            if (target.FullName != "System.StringComparer" && target.GetAllBaseTypes().Any(b => b.GetDefinition()?.FullName == "System.StringComparer")) cast.ReplaceWith(cast.Expression.Clone());
        }
    }
}
