using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Resolver;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;
using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>CIL 允许、C# 不允许的表达式形式，改写成语义相同的合法写法。</summary>
    private sealed class ExpressionForms : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            ExtensionAwaitUsings(rootNode);
            foreach (var type in rootNode.Descendants.OfType<SimpleType>().ToArray()) SharedSelfType(type);
            // 改写时会复制子树：先处理内层，复制到的才是改好的节点。
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().Reverse().ToArray()) SharedCast(cast);
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().Reverse().ToArray()) GenericCast(cast);
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().Reverse().ToArray()) FirstFieldCast(cast);
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().Where(c => c.Expression is NullReferenceExpression).ToArray()) GuardedReceiver(cast);
            foreach (var cast in rootNode.Descendants.OfType<CastExpression>().Where(c => c.Expression is NullReferenceExpression).ToArray()) NullReceiver(cast);
            foreach (var call in rootNode.Descendants.OfType<InvocationExpression>().Reverse().ToArray())
            {
                Placeholder(call);
                DecimalMinMax(call);
                SharedTypeArguments(call);
                DelegateArguments(call, context);
                AmbiguousNamedArguments(call);
                SkipLevelCall(call, context);
            }
            foreach (var direction in rootNode.Descendants.OfType<DirectionExpression>().ToArray()) ReadOnlyParameterByReference(direction);
            foreach (var statement in rootNode.Descendants.OfType<ThrowStatement>().ToArray()) ThrowObject(statement);
            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray()) ReferenceLocal(declaration);
            foreach (var lambda in rootNode.Descendants.Where(n => n is LambdaExpression or AnonymousMethodExpression).ToArray()) StructCapture(lambda, context);
            foreach (var text in rootNode.Descendants.OfType<InterpolatedStringExpression>().ToArray()) MultilineInterpolation(text);
        }

        /// <summary>
        /// 结构体方法里的 lambda 不能访问 this（CS1673）。没提升的状态机把闭包对象存在字段里，lambda 只读这个字段：
        /// 先复制到局部再捕获，闭包对象是同一个引用。值类型字段的副本和原字段互不影响，lambda 写它时不改写。
        /// </summary>
        private static void StructCapture(AstNode lambda, TransformContext context)
        {
            if (lambda.GetParent<TypeDeclaration>() is not { ClassType: ClassType.Struct } || lambda.GetParent<EntityDeclaration>() is not { } entity || entity.HasModifier(Modifiers.Static)) return;
            if (lambda.Ancestors.Any(a => a is LambdaExpression or AnonymousMethodExpression)) return;
            var anchor = lambda.Ancestors.OfType<Statement>().FirstOrDefault(s => s.Parent is BlockStatement or SwitchSection);
            if (anchor is null) return;
            var fields = new Dictionary<string, string>();
            var occupied = entity.Descendants.OfType<VariableInitializer>().Select(v => v.Name).ToHashSet();
            foreach (var use in lambda.Descendants.OfType<Expression>().ToArray())
            {
                var field = use switch
                {
                    IdentifierExpression identifier => identifier.Annotation<MemberResolveResult>()?.Member as IField,
                    MemberReferenceExpression { Target: ThisReferenceExpression } member => member.Annotation<MemberResolveResult>()?.Member as IField,
                    _ => null,
                };
                if (field is null || field.IsStatic || field.ReturnType.IsReferenceType != true && Written(use)) continue;
                if (!fields.TryGetValue(field.Name, out var local))
                {
                    var number = 1;
                    do local = field.Name + "Capture" + (number++ == 1 ? "" : number - 1); while (!occupied.Add(local));
                    fields.Add(field.Name, local);
                    var declaration = new VariableDeclarationStatement(QualifiedTypes.ConvertType(field.ReturnType), local, new IdentifierExpression(field.Name));
                    if (anchor.Parent is BlockStatement block) block.Statements.InsertBefore(anchor, declaration);
                    else ((SwitchSection)anchor.Parent!).Statements.InsertBefore(anchor, declaration);
                }
                use.ReplaceWith(new IdentifierExpression(local));
            }
        }

        /// <summary>await 经扩展方法取等待器时，声明它的命名空间只出现在被隐藏的调用里，要补 using。</summary>
        private static void ExtensionAwaitUsings(AstNode rootNode)
        {
            if (rootNode is not SyntaxTree tree) return;
            var present = tree.Members.OfType<UsingDeclaration>().Select(u => u.Namespace).ToHashSet();
            var needed = rootNode.Descendants.OfType<UnaryOperatorExpression>().Where(u => u.Operator == UnaryOperatorType.Await)
                .Select(u => u.Annotation<ICSharpCode.Decompiler.IL.Await>()?.GetAwaiterMethod).Where(m => m is { IsStatic: true }).Select(m => m!.DeclaringType.Namespace)
                .Where(n => !string.IsNullOrEmpty(n) && !present.Contains(n)).Distinct().ToArray();
            foreach (var name in needed)
            {
                AstType import = new SimpleType(name.Split('.')[0]);
                foreach (var part in name.Split('.').Skip(1)) import = new MemberType(import, part);
                tree.Members.InsertBefore(tree.Members.FirstOrDefault(), new UsingDeclaration { Import = import });
            }
        }

        /// <summary>C# 9 的非逐字内插字符串里不能换行（CS8967）。内插表达式会写成多行（对象初始值、lambda）时改用 string.Format。</summary>
        private static void MultilineInterpolation(InterpolatedStringExpression text)
        {
            var parts = text.Content.ToArray();
            if (!parts.OfType<Interpolation>().Any(i => i.Expression is not null && i.Expression.DescendantsAndSelf.Any(n => n is ArrayInitializerExpression or LambdaExpression or AnonymousMethodExpression or SwitchExpression))) return;
            var format = new System.Text.StringBuilder();
            var arguments = new List<Expression>();
            foreach (var part in parts)
            {
                if (part is InterpolatedStringText literal) format.Append(System.Text.RegularExpressions.Regex.Unescape(literal.Text ?? ""));
                else if (part is Interpolation interpolation)
                {
                    format.Append('{').Append(arguments.Count);
                    if (interpolation.Alignment != 0) format.Append(',').Append(interpolation.Alignment);
                    if (!string.IsNullOrEmpty(interpolation.Suffix)) format.Append(':').Append(interpolation.Suffix);
                    format.Append('}');
                    arguments.Add(interpolation.Expression!.Clone());
                }
            }
            var call = new InvocationExpression(new MemberReferenceExpression(new TypeReferenceExpression(new PrimitiveType("string")), "Format"), new PrimitiveExpression(format.ToString()));
            call.Arguments.AddRange(arguments);
            text.ReplaceWith(call);
        }

        /// <summary>类型参数和具体类型之间没有直接的强制转换（CS0030），经 object 转换：共享泛型的 CIL 本来就按实际类型读。</summary>
        private static void GenericCast(CastExpression cast)
        {
            var from = StaticType(cast.Expression);
            if (from?.Kind == TypeKind.TypeParameter && cast.Type is PrimitiveType { Keyword: not "object" })
            {
                cast.Expression = new CastExpression(new PrimitiveType("object"), cast.Expression.Clone());
                return;
            }
            var to = cast.Type.Annotation<ResolveResult>()?.Type ?? cast.Annotation<ResolveResult>()?.Type;
            if (from is null || to is null || from.Kind == TypeKind.Unknown || to.Kind == TypeKind.Unknown) return;
            if (from.Kind != TypeKind.TypeParameter && to.Kind != TypeKind.TypeParameter) return;
            if (from.IsKnownType(KnownTypeCode.Object) || to.IsKnownType(KnownTypeCode.Object) || from.Equals(to)) return;
            if (from.Kind == TypeKind.Interface || to.Kind == TypeKind.Interface) return;
            cast.Expression = new CastExpression(new PrimitiveType("object"), cast.Expression.Clone());
        }

        private static IType? StaticType(Expression expression) => expression is IdentifierExpression identifier && identifier.GetILVariable() is { } variable
            ? variable.Type
            : expression.Annotation<ResolveResult>()?.Type;

        private static bool IsSharedInstance(IType type) => type.TypeArguments.Any(a => a.IsKnownType(KnownTypeCode.Object) || IsSharedInstance(a));

        private static bool RestrictsObject(ITypeParameter parameter) =>
            parameter.DirectBaseTypes.Any(t => !t.IsKnownType(KnownTypeCode.Object) && !t.IsKnownType(KnownTypeCode.ValueType));

        /// <summary>
        /// 共享泛型的实参恢复成 object。类型内部的 C&lt;object&gt; 违反 C 自己的约束时不可能是原写法（CS0311），就是 C&lt;T&gt;。
        /// </summary>
        private static void SharedSelfType(SimpleType type)
        {
            if (type.TypeArguments.Count == 0 || !type.TypeArguments.All(a => a is PrimitiveType { Keyword: "object" })) return;
            var owner = type.Ancestors.OfType<TypeDeclaration>().FirstOrDefault(t => t.Name == type.Identifier && t.TypeParameters.Count == type.TypeArguments.Count);
            if (owner is null || !owner.Constraints.Any(c => c.BaseTypes.Any(b => b is not PrimitiveType))) return;
            type.TypeArguments.Clear();
            foreach (var parameter in owner.TypeParameters) type.TypeArguments.Add(new SimpleType(parameter.Name));
        }

        /// <summary>(C&lt;object&gt;)(object)x，x 的类型本来就继承 C：共享泛型的实例，直接用 x。委托和泛型方法的实参没有 (object) 也一样。</summary>
        private static void SharedCast(CastExpression cast)
        {
            var viaObject = cast.Expression as CastExpression is { Type: PrimitiveType { Keyword: "object" } };
            var inner = viaObject ? ((CastExpression)cast.Expression).Expression : cast.Expression;
            var target = cast.Annotation<ResolveResult>()?.Type ?? cast.Type.Annotation<ResolveResult>()?.Type;
            var source = StaticType(inner);
            if (target?.GetDefinition() is not { } definition || source is null) return;
            // 具体化的代码把委托转换成实际实参的实例；委托的调用由 DelegateArguments 按原类型改写。
            if (!IsSharedInstance(target) && !(viaObject && target.Kind == TypeKind.Delegate && MentionsTypeParameter(source))) return;
            // 作为泛型方法的实参时，共享实例的转换会让类型推断冲突（CS0411）。
            var isInferred = cast.Parent is InvocationExpression call && call.Target != cast && call.Annotation<ResolveResult>() is InvocationResolveResult { Member: IMethod { TypeArguments.Count: > 0 } };
            if (!viaObject && target.Kind != TypeKind.Delegate && !isInferred) return;
            if (source.GetAllBaseTypes().Any(b => definition.Equals(b.GetDefinition()))) cast.ReplaceWith(inner.Clone());
        }

        /// <summary>M&lt;object&gt;((object)x) 违反 M 的约束时同样是共享泛型：去掉转换，由 x 的类型推断实参。</summary>
        private static void SharedTypeArguments(InvocationExpression call)
        {
            if (call.Target is not MemberReferenceExpression member || member.TypeArguments.Count == 0 || !member.TypeArguments.All(a => a is PrimitiveType { Keyword: "object" })) return;
            if (call.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod method } || !method.TypeParameters.Any(RestrictsObject)) return;
            foreach (var argument in call.Arguments.OfType<CastExpression>().ToArray())
                if (argument.Type is PrimitiveType { Keyword: "object" } || argument.Type.DescendantsAndSelf.OfType<PrimitiveType>().Any(t => t.Keyword == "object")) argument.ReplaceWith(argument.Expression.Clone());
            member.TypeArguments.Clear();
        }

        /// <summary>
        /// 共享泛型的委托调用按 object 传值；委托实际的形参是类型参数时，同类型的值去掉 (object)，
        /// 具体化代码里实际类型的值（CS1503）经 object 转换。
        /// </summary>
        private static void DelegateArguments(InvocationExpression call, TransformContext context)
        {
            var receiver = call.Target switch
            {
                MemberReferenceExpression { MemberName: "Invoke", Target: UnaryOperatorExpression { Operator: UnaryOperatorType.NullConditional, Expression: var conditional } } => conditional,
                MemberReferenceExpression { MemberName: "Invoke", Target: var plain } => plain,
                MemberReferenceExpression => null,
                var direct => direct,
            };
            if (receiver is null || StaticType(receiver) is not { Kind: TypeKind.Delegate } type || type.GetDelegateInvokeMethod() is not { } method) return;
            var arguments = call.Arguments.ToArray();
            if (arguments.Length != method.Parameters.Count) return;
            var conversions = CSharpConversions.Get(context.TypeSystem);
            for (var i = 0; i < arguments.Length; i++)
            {
                var parameter = method.Parameters[i].Type;
                if (!MentionsTypeParameter(parameter)) continue;
                if (arguments[i] is CastExpression { Type: PrimitiveType { Keyword: "object" }, Expression: var value } && parameter.Equals(StaticType(value)))
                {
                    arguments[i].ReplaceWith(value.Clone());
                    continue;
                }
                if (arguments[i] is CastExpression { Expression: CastExpression { Type: PrimitiveType { Keyword: "object" }, Expression: var specialized } } && parameter.Equals(StaticType(specialized)))
                {
                    arguments[i].ReplaceWith(specialized.Clone());
                    continue;
                }
                if (StaticType(arguments[i]) is not { Kind: not TypeKind.Unknown and not TypeKind.Null } argument) continue;
                if (argument.Equals(parameter) || conversions.ImplicitConversion(argument, parameter).IsValid) continue;
                var inner = arguments[i] is CastExpression { Type: not PrimitiveType, Expression: CastExpression { Type: PrimitiveType { Keyword: "object" }, Expression: var shared } } ? shared : arguments[i];
                arguments[i].ReplaceWith(new CastExpression(QualifiedTypes.ConvertType(parameter), new CastExpression(new PrimitiveType("object"), inner.Clone())));
            }
        }

        private static bool MentionsTypeParameter(IType type) => type.Kind == TypeKind.TypeParameter || type.TypeArguments.Any(MentionsTypeParameter);

        /// <summary>内联的 Math.Min(decimal, decimal) 留下内部的 decimal.Min(in, in)，语言不能直接调用（CS0570）。</summary>
        private static void DecimalMinMax(InvocationExpression call)
        {
            if (call.Target is not MemberReferenceExpression { MemberName: "Min" or "Max", Target: TypeReferenceExpression { Type: PrimitiveType { Keyword: "decimal" } } } target) return;
            var arguments = call.Arguments.ToArray();
            if (arguments.Length != 2 || !arguments.All(a => a is DirectionExpression)) return;
            var math = new TypeReferenceExpression(new MemberType(new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true }, "Math"));
            call.ReplaceWith(new InvocationExpression(new MemberReferenceExpression(math, target.MemberName), arguments.Select(a => ((DirectionExpression)a).Expression.Clone())));
        }

        /// <summary>
        /// 命名实参让形参名相同、顺序不同的重载无法区分（CS0121），按形参顺序写。
        /// 反编译器用命名实参保留求值顺序，这里调整顺序只在实参有副作用时才可观察。
        /// </summary>
        private static void AmbiguousNamedArguments(InvocationExpression call)
        {
            if (!call.Arguments.Any(a => a is NamedArgumentExpression)) return;
            if (call.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod method } || method.DeclaringTypeDefinition is not { } owner) return;
            var names = method.Parameters.Select(p => p.Name).ToHashSet();
            if (owner.Methods.Count(m => m.Name == method.Name && m.Parameters.Count == names.Count && names.SetEquals(m.Parameters.Select(p => p.Name))) < 2) return;
            var arguments = call.Arguments.ToArray();
            var named = arguments.OfType<NamedArgumentExpression>().ToDictionary(n => n.Name);
            var positional = arguments.TakeWhile(a => a is not NamedArgumentExpression).ToArray();
            if (positional.Length + named.Count != method.Parameters.Count) return;
            var ordered = method.Parameters.Select((p, i) => i < positional.Length ? positional[i].Clone() : named.TryGetValue(p.Name, out var n) ? n.Expression.Clone() : null).ToArray();
            if (ordered.Any(o => o is null)) return;
            call.Arguments.Clear();
            call.Arguments.AddRange(ordered!);
        }

        /// <summary>
        /// 内联中间类的方法后可能留下跨过中间重写的非虚调用，C# 没有对应写法（CS1540），base 又会进入中间重写。
        /// 经函数指针调用保持非虚语义。
        /// </summary>
        private static void SkipLevelCall(InvocationExpression call, TransformContext context)
        {
            if (call.Target is not MemberReferenceExpression { Target: CastExpression { Expression: var receiver } }) return;
            if (call.Annotation<ResolveResult>() is not InvocationResolveResult { Member: IMethod method } || method.IsStatic) return;
            if (method.Accessibility is not (Accessibility.Protected or Accessibility.ProtectedOrInternal or Accessibility.ProtectedAndInternal)) return;
            if (receiver is not ThisReferenceExpression && StaticType(receiver)?.GetAllBaseTypes().Any(b => method.DeclaringTypeDefinition!.Equals(b.GetDefinition())) != true) return;
            if (call.GetParent<EntityDeclaration>() is not { } entity || entity.Descendants.Any(d => d is YieldReturnStatement or YieldBreakStatement)) return;
            var isAsync = entity.HasModifier(Modifiers.Async) || call.Ancestors.Any(a => a is LambdaExpression { IsAsync: true } or AnonymousMethodExpression { IsAsync: true });
            if (isAsync && call.Parent is not ExpressionStatement) return;
            if (MemberTokens.Reflection(method, context) is not { } lookup) return;
            var pointer = new FunctionPointerAstType { ReturnType = QualifiedTypes.ConvertType(method.ReturnType) };
            pointer.Parameters.Add(new ParameterDeclaration { Type = QualifiedTypes.ConvertType(method.DeclaringType) });
            foreach (var parameter in method.Parameters) pointer.Parameters.Add(new ParameterDeclaration { Type = QualifiedTypes.ConvertType(parameter.Type) });
            var address = new InvocationExpression(new MemberReferenceExpression(new MemberReferenceExpression(lookup, "MethodHandle"), "GetFunctionPointer"));
            var arguments = new List<Expression> { receiver.Clone() };
            arguments.AddRange(call.Arguments.Select(a => a.Clone()));
            var direct = new InvocationExpression(new ParenthesizedExpression(new CastExpression(pointer, address)), arguments);
            if (isAsync)
            {
                var block = new BlockStatement();
                block.Statements.Add(new ExpressionStatement(direct));
                call.Parent!.ReplaceWith(new UnsafeStatement { Body = block });
                return;
            }
            call.ReplaceWith(direct);
            entity.Modifiers |= Modifiers.Unsafe;
        }

        /// <summary>内联把 in 形参的地址当 ref 用（CS8329）。被调方法只读这个值，传一份副本。</summary>
        private static void ReadOnlyParameterByReference(DirectionExpression direction)
        {
            if (direction.FieldDirection != FieldDirection.Ref || direction.Expression is not IdentifierExpression identifier || direction.GetParent<EntityDeclaration>() is not { } entity) return;
            var (parameters, body) = entity switch
            {
                MethodDeclaration m => (m.Parameters, m.Body),
                ConstructorDeclaration c => (c.Parameters, c.Body),
                OperatorDeclaration o => (o.Parameters, o.Body),
                _ => (null, null),
            };
            if (parameters?.FirstOrDefault(p => p.Name == identifier.Identifier && p.ParameterModifier == ReferenceKind.In) is not { Name: { } name } parameter || body is null) return;
            var copy = name + "Copy";
            if (!body.Statements.OfType<VariableDeclarationStatement>().Any(d => d.Variables.Any(v => v.Name == copy)))
                body.Statements.InsertBefore(body.Statements.FirstOrDefault(), new VariableDeclarationStatement(parameter.Type!.Clone(), copy, new IdentifierExpression(name)));
            direction.Expression = new IdentifierExpression(copy);
        }

        /// <summary>结构体 this 按第一个字段的类型读取，等于读这个字段：偏移都是 0。</summary>
        private static void FirstFieldCast(CastExpression cast)
        {
            if (cast.Expression is not ThisReferenceExpression) return;
            if (cast.GetParent<TypeDeclaration>()?.Annotation<TypeResolveResult>()?.Type.GetDefinition() is not { Kind: TypeKind.Struct } owner) return;
            var target = cast.Annotation<ResolveResult>()?.Type ?? cast.Type.Annotation<ResolveResult>()?.Type;
            if (target is null || owner.Fields.FirstOrDefault(f => !f.IsStatic) is not { } first || !first.ReturnType.Equals(target)) return;
            const string backing = ">k__BackingField";
            var name = first.Name.EndsWith(backing, StringComparison.Ordinal) ? first.Name[1..^backing.Length] : first.Name;
            cast.ReplaceWith(new MemberReferenceExpression(new ThisReferenceExpression(), name));
        }

        /// <summary>
        /// 被调方法不用 this 时 clang 去掉了接收者的计算，只留下 IL2CPP 的判空，CIL 是判空后接 ((T)null).M()。
        /// C# 的实例调用会对接收者判空，这样写运行时必抛异常。前面判空的对象就是原来的接收者：写回去，紧邻的判空合并进调用。
        /// </summary>
        private static void GuardedReceiver(CastExpression cast)
        {
            if (cast.Parent is not MemberReferenceExpression member || member.Target != cast) return;
            var target = (cast.Annotation<ResolveResult>()?.Type ?? cast.Type.Annotation<ResolveResult>()?.Type)?.GetDefinition();
            var statement = cast.Ancestors.OfType<Statement>().FirstOrDefault(a => a.Parent is BlockStatement);
            if (target is null || statement?.Parent is not BlockStatement block) return;
            var before = block.Statements.TakeWhile(a => a != statement).Reverse().Take(8).ToArray();
            for (var i = 0; i < before.Length; i++)
            {
                if (before[i] is not IfElseStatement { FalseStatement: null, TrueStatement: BlockStatement { Statements: { Count: 1 } thrown }, Condition: BinaryOperatorExpression { Operator: BinaryOperatorType.Equality, Left: { } left, Right: NullReferenceExpression } } guard
                    || thrown.First() is not ThrowStatement { Expression: ObjectCreateExpression { Type: var exception } } || !exception.ToString().EndsWith("NullReferenceException", StringComparison.Ordinal)) continue;
                var receiver = left is CastExpression { Type: PrimitiveType { Keyword: "object" }, Expression: { } inner } ? inner : left;
                if (!IsStableRead(receiver)) continue;
                var type = receiver is ThisReferenceExpression ? cast.GetParent<TypeDeclaration>()?.Annotation<TypeResolveResult>()?.Type : StaticType(receiver);
                if (type is null || !type.GetAllBaseTypes().Any(b => target.Equals(b.GetDefinition()))) continue;
                // 判空和使用之间改过这个对象时不能合并。
                if (before.Take(i).Any(s => s.Descendants.OfType<IdentifierExpression>().Any(id => Written(id) && receiver.DescendantsAndSelf.OfType<IdentifierExpression>().Any(r => r.Identifier == id.Identifier)))) return;
                cast.ReplaceWith(receiver.Clone());
                if (i == 0) guard.Remove();
                return;
            }
        }

        private static bool IsStableRead(Expression expression) => expression switch
        {
            ThisReferenceExpression or IdentifierExpression => true,
            MemberReferenceExpression { Target: { } target } member => member.Annotation<MemberResolveResult>()?.Member is IField && IsStableRead(target),
            _ => false,
        };

        /// <summary>
        /// 被调方法不用 this 时 clang 不准备接收者，恢复成 ((T)null).M()。调用方自己是 T 或其派生类时，
        /// 接收者写成 this：原方法体用不到它，而空接收者在共享泛型上还写不出合法的类型实参。
        /// </summary>
        private static void NullReceiver(CastExpression cast)
        {
            if (cast.Parent is not MemberReferenceExpression member || member.Target != cast) return;
            if (cast.GetParent<EntityDeclaration>() is not { } entity || entity.HasModifier(Modifiers.Static)) return;
            var owner = cast.GetParent<TypeDeclaration>()?.Annotation<TypeResolveResult>()?.Type.GetDefinition();
            var target = (cast.Type.Annotation<ResolveResult>()?.Type ?? cast.Annotation<ResolveResult>()?.Type)?.GetDefinition();
            if (owner is null || target is null || owner.Kind == TypeKind.Struct) return;
            if (owner.Equals(target) || owner.IsDerivedFrom(target)) cast.ReplaceWith(new ThisReferenceExpression());
        }

        /// <summary>占位值 Unrecovered.Value&lt;T&gt; 的 T 不能是按引用、指针或按引用结构体。</summary>
        private static void Placeholder(InvocationExpression call)
        {
            if (call.Target is not MemberReferenceExpression { MemberName: "Value", Target: TypeReferenceExpression { Type: var owner }, TypeArguments: { Count: 1 } arguments } member
                || !owner.ToString().EndsWith("Unrecovered", StringComparison.Ordinal)) return;
            var argument = arguments.First();
            if (argument is ComposedType { HasRefSpecifier: true } reference)
            {
                member.MemberName = "Ref";
                reference.HasRefSpecifier = false;
                reference.HasReadOnlySpecifier = false;
            }
            else if (argument is ComposedType { PointerRank: > 0 })
            {
                var pointer = argument.Clone();
                arguments.Clear();
                arguments.Add(new PrimitiveType("nint"));
                call.ReplaceWith(new CastExpression(pointer, call.Clone()));
            }
            else if ((argument.Annotation<ResolveResult>()?.Type ?? call.Annotation<ResolveResult>()?.Type)?.GetDefinition() is { IsByRefLike: true })
                call.ReplaceWith(new DefaultValueExpression(argument.Clone()));
        }

        /// <summary>CIL 可以抛任意对象引用，C# 只能抛 Exception（CS0029）。</summary>
        private static void ThrowObject(ThrowStatement statement)
        {
            if (statement.Expression is null || statement.Expression.Annotation<ResolveResult>()?.Type is not { } type || !type.IsKnownType(KnownTypeCode.Object)) return;
            statement.Expression = new CastExpression(new MemberType(new MemberType(new SimpleType("global"), "System") { IsDoubleColon = true }, "Exception"), statement.Expression.Clone());
        }

        /// <summary>
        /// 拆箱结果不能绑定成 ref 局部（CS0445），async 和迭代器里也不能有 ref 局部（C# 9，CS8773）。
        /// 绑定目标稳定时把用处换回目标本身；否则这个局部只被读取或重新绑定时改成普通局部，读取的是绑定时的值。
        /// </summary>
        private static void ReferenceLocal(VariableDeclarationStatement declaration)
        {
            if (declaration.Type is not ComposedType { HasRefSpecifier: true } || declaration.Variables.Count != 1) return;
            var variable = declaration.Variables.First();
            var value = (variable.Initializer as DirectionExpression)?.Expression;
            var function = declaration.Ancestors.FirstOrDefault(a => a is LambdaExpression or AnonymousMethodExpression or EntityDeclaration);
            if (function is null) return;
            var isAsync = function is MethodDeclaration m && (m.HasModifier(Modifiers.Async) || m.Descendants.Any(d => d is YieldReturnStatement or YieldBreakStatement))
                || function is LambdaExpression { IsAsync: true } || function is AnonymousMethodExpression { IsAsync: true };
            var uses = function.Descendants.OfType<IdentifierExpression>().Where(i => i.Identifier == variable.Name).ToArray();
            var rebinds = uses.Where(u => u.Parent is AssignmentExpression { Right: DirectionExpression } a && a.Left == u).ToArray();
            // 只读字段不能按引用绑定（CS0198）。
            var bindsReadOnly = rebinds.Select(r => ((AssignmentExpression)r.Parent!).Right).Prepend(variable.Initializer).OfType<DirectionExpression>()
                .Any(d => d.Expression.Annotation<MemberResolveResult>()?.Member is IField { IsReadOnly: true });
            if (!isAsync && !bindsReadOnly && value is not CastExpression) return;
            if (isAsync && value is not null && rebinds.Length == 0 && Stable(value, function))
            {
                foreach (var use in uses) use.ReplaceWith(value.Clone());
                declaration.Remove();
                return;
            }
            if (uses.Except(rebinds).Any(Written)) return;
            foreach (var rebind in rebinds)
            {
                var assignment = (AssignmentExpression)rebind.Parent!;
                assignment.Right = Direct(assignment.Right.Clone());
            }
            var type = (ComposedType)declaration.Type.Clone();
            type.HasRefSpecifier = false;
            type.HasReadOnlySpecifier = false;
            declaration.Type = type.BaseType.Clone() is var element && type.PointerRank == 0 && !type.ArraySpecifiers.Any() && !type.HasNullableSpecifier ? element : type;
            variable.Initializer = value is null ? null! : Direct(value.Clone());
        }

        /// <summary>字段链的根是 this 或没有被重新赋值的局部：每次求值得到同一个位置。</summary>
        private static bool Stable(Expression value, AstNode function)
        {
            var root = value;
            while (root is MemberReferenceExpression member) root = member.Target;
            if (root is ThisReferenceExpression or BaseReferenceExpression or TypeReferenceExpression) return true;
            if (root is not IdentifierExpression identifier) return false;
            if (identifier.Annotation<MemberResolveResult>() is not null) return true;
            return !function.Descendants.OfType<IdentifierExpression>().Any(i => i.Identifier == identifier.Identifier && Written(i));
        }

        private static Expression Direct(Expression value) => value switch
        {
            ConditionalExpression conditional => new ConditionalExpression(conditional.Condition.Clone(), Direct(conditional.TrueExpression.Clone()), Direct(conditional.FalseExpression.Clone())),
            DirectionExpression direction => Direct(direction.Expression.Clone()),
            _ => value,
        };

        private static bool Written(Expression use)
        {
            AstNode node = use;
            while (node.Parent is MemberReferenceExpression member && member.Target == node) node = member;
            return node.Parent switch
            {
                AssignmentExpression assignment => assignment.Left == node,
                UnaryOperatorExpression { Operator: UnaryOperatorType.Increment or UnaryOperatorType.Decrement or UnaryOperatorType.PostIncrement or UnaryOperatorType.PostDecrement or UnaryOperatorType.AddressOf } => true,
                DirectionExpression => true,
                _ => false,
            };
        }
    }
}
