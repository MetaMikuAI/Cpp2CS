using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;
using TypeKind = ICSharpCode.Decompiler.TypeSystem.TypeKind;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// CIL 的局部从零开始，C# 要求读之前确定赋值（CS0165）、out 形参在返回前赋值（CS0177）、ref 局部声明时初始化（CS8174）。
    /// 按 C# 的规则分析结构化语句，只给确实需要的局部补默认值：这正是 CIL 的初值，语义不变。
    /// </summary>
    private sealed class DefiniteAssignment : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var entity in rootNode.Descendants.OfType<EntityDeclaration>())
            {
                switch (entity)
                {
                    case MethodDeclaration { Body: not null } method: new Flow(method.Body, method.Parameters).Apply(); break;
                    case ConstructorDeclaration { Body: not null } constructor: new Flow(constructor.Body, constructor.Parameters).Apply(); break;
                    case OperatorDeclaration { Body: not null } @operator: new Flow(@operator.Body, @operator.Parameters).Apply(); break;
                    case DestructorDeclaration { Body: not null } destructor: new Flow(destructor.Body, []).Apply(); break;
                    case Accessor { Body: not null } accessor: new Flow(accessor.Body, []).Apply(); break;
                }
            }
            foreach (var declaration in rootNode.Descendants.OfType<VariableDeclarationStatement>().ToArray()) BindHolder(declaration);
        }

        /// <summary>按引用的局部必须声明时绑定；真实绑定在后面的赋值里。占位是同作用域的局部，这样重新绑定到 this 或局部时不超出它的转义范围。</summary>
        private static void BindHolder(VariableDeclarationStatement declaration)
        {
            if (declaration.Type is not ComposedType { HasRefSpecifier: true } composed) return;
            foreach (var variable in declaration.Variables.Where(v => v.Initializer is null))
            {
                var element = (ComposedType)composed.Clone();
                element.HasRefSpecifier = false;
                element.HasReadOnlySpecifier = false;
                var holder = variable.Name + "Holder";
                var type = element is { PointerRank: 0, HasNullableSpecifier: false } && !element.ArraySpecifiers.Any() ? element.BaseType.Clone() : element;
                var local = new VariableDeclarationStatement(type, holder, new DefaultValueExpression(null!));
                switch (declaration.Parent)
                {
                    case BlockStatement block: block.Statements.InsertBefore(declaration, local); break;
                    case SwitchSection section: section.Statements.InsertBefore(declaration, local); break;
                    default: continue;
                }
                variable.Initializer = new DirectionExpression(FieldDirection.Ref, new IdentifierExpression(holder));
                HoistBindingTargets(variable.Name, local);
            }
        }

        /// <summary>ref 局部重新绑定到更窄作用域的局部（CS8374）：CIL 的局部只有一个存储位置，把目标提到和占位相同的作用域。</summary>
        private static void HoistBindingTargets(string name, VariableDeclarationStatement anchor)
        {
            var function = EnclosingFunction(anchor)!;
            var targets = function.Descendants.OfType<AssignmentExpression>()
                .Where(a => a.Left is IdentifierExpression target && target.Identifier == name)
                .Select(a => a.Right).OfType<DirectionExpression>().Select(d => d.Expression).OfType<IdentifierExpression>().Select(t => t.Identifier).Distinct().ToArray();
            foreach (var target in targets)
            {
                var declaration = function.Descendants.OfType<VariableDeclarationStatement>().FirstOrDefault(d => d.Variables.Count == 1 && d.Variables.First().Name == target);
                if (declaration is null || declaration.Parent == anchor.Parent || !declaration.Ancestors.Contains(anchor.Parent)) continue;
                var value = declaration.Variables.First().Initializer;
                var type = declaration.Type.Clone();
                if (value is null) declaration.Remove();
                else declaration.ReplaceWith(new ExpressionStatement(new AssignmentExpression(new IdentifierExpression(target), value.Clone())));
                var isReference = type is ComposedType { HasRefSpecifier: true };
                var hoisted = isReference ? new VariableDeclarationStatement(type, target) : new VariableDeclarationStatement(type, target, new DefaultValueExpression(null!));
                if (anchor.Parent is BlockStatement block) block.Statements.InsertBefore(anchor, hoisted);
                else ((ICSharpCode.Decompiler.CSharp.Syntax.SwitchSection)anchor.Parent!).Statements.InsertBefore(anchor, hoisted);
                if (isReference) BindHolder(hoisted);
            }
        }

        /// <summary>一个函数体的流分析。assigned 为空表示不可达（任何变量都算已赋值）。</summary>
        private sealed class Flow(BlockStatement body, IEnumerable<ParameterDeclaration> parameters)
        {
            private readonly Dictionary<string, VariableInitializer> current = [];
            private readonly HashSet<string> outParameters = parameters.Where(p => p.ParameterModifier == ReferenceKind.Out).Select(p => p.Name!).ToHashSet();
            private readonly HashSet<VariableInitializer> needsDefault = [];
            private readonly HashSet<string> outNeedsDefault = [];
            private readonly HashSet<string> tracked = [];
            private Dictionary<string, HashSet<string>?> labels = [];
            private Dictionary<string, HashSet<string>?> labelsNext = [];
            private Stack<List<HashSet<string>>> breaks = new();
            private Stack<List<HashSet<string>>> continues = new();
            private HashSet<string>? state = [];

            public void Apply()
            {
                var hasLabels = body.Descendants.OfType<LabelStatement>().Any();
                for (var round = 0; round < (hasLabels ? 64 : 1); round++)
                {
                    needsDefault.Clear();
                    outNeedsDefault.Clear();
                    labelsNext = [];
                    tracked.Clear();
                    foreach (var name in outParameters) tracked.Add(name);
                    state = [];
                    Exec(body);
                    Exit();
                    if (!hasLabels || Same(labels, labelsNext)) break;
                    labels = labelsNext;
                }
                foreach (var variable in needsDefault) Initialize(variable, hasLabels);
                foreach (var name in outNeedsDefault)
                    body.Statements.InsertBefore(body.Statements.FirstOrDefault(), new ExpressionStatement(new AssignmentExpression(new IdentifierExpression(name), new DefaultValueExpression(null!))));
            }

            /// <summary>
            /// 补默认值。goto 或 switch 可能跳过声明时，声明处的初始化不算赋值，要提到函数开头：
            /// CIL 的局部本来就在方法入口清零，只有一个存储位置。
            /// </summary>
            private void Initialize(VariableInitializer variable, bool hasLabels)
            {
                if (variable.Parent is not VariableDeclarationStatement { Variables.Count: 1 } declaration || declaration.Type is ComposedType { HasRefSpecifier: true }) return;
                if (!hasLabels && declaration.Parent is BlockStatement && variable.Initializer is null)
                {
                    variable.Initializer = new DefaultValueExpression(null!);
                    return;
                }
                if (declaration.Parent is not (BlockStatement or SwitchSection)) return;
                var function = FunctionBody(declaration);
                var scope = function.Descendants.OfType<VariableInitializer>().Count(v => v.Name == variable.Name) == 1 ? function : declaration.GetParent<BlockStatement>()!;
                if (variable.Initializer is { } value) declaration.ReplaceWith(new ExpressionStatement(new AssignmentExpression(new IdentifierExpression(variable.Name), value.Clone())));
                else declaration.Remove();
                scope.Statements.InsertBefore(scope.Statements.FirstOrDefault(), new VariableDeclarationStatement(declaration.Type.Clone(), variable.Name, new DefaultValueExpression(null!)));
            }

            private static BlockStatement FunctionBody(AstNode node) =>
                node.Ancestors.OfType<BlockStatement>().First(b => b.Parent is LambdaExpression or AnonymousMethodExpression or EntityDeclaration or Accessor);

            private static bool Same(Dictionary<string, HashSet<string>?> a, Dictionary<string, HashSet<string>?> b) =>
                a.Count == b.Count && a.All(p => b.TryGetValue(p.Key, out var other) && (p.Value is null ? other is null : other is not null && p.Value.SetEquals(other)));

            private void Exit()
            {
                if (state is null) return;
                foreach (var name in outParameters.Where(n => !state.Contains(n))) outNeedsDefault.Add(name);
            }

            private static HashSet<string>? Join(HashSet<string>? a, HashSet<string>? b)
            {
                if (a is null) return b is null ? null : new HashSet<string>(b);
                if (b is null) return new HashSet<string>(a);
                var result = new HashSet<string>(a);
                result.IntersectWith(b);
                return result;
            }

            private HashSet<string>? Copy() => state is null ? null : new HashSet<string>(state);

            private void Exec(AstNode? node)
            {
                if (node is null) return;
                switch (node)
                {
                    case BlockStatement block:
                        foreach (var statement in block.Statements) Exec(statement);
                        break;
                    case LabelStatement label:
                        // 上一轮记录的所有跳转状态并入；第一轮按乐观假设（未知的跳转不限制）。
                        if (labels.TryGetValue(label.Label!, out var incoming)) state = Join(state, incoming);
                        else if (state is null) state = new HashSet<string>(tracked);
                        break;
                    case GotoStatement jump:
                        labelsNext[jump.Label!] = labelsNext.TryGetValue(jump.Label!, out var known) ? Join(known, state) : Copy();
                        state = null;
                        break;
                    case GotoCaseStatement or GotoDefaultStatement:
                        state = null;
                        break;
                    case VariableDeclarationStatement declaration:
                        foreach (var variable in declaration.Variables)
                        {
                            current[variable.Name] = variable;
                            tracked.Add(variable.Name);
                            if (variable.Initializer is not null)
                            {
                                Eval(variable.Initializer);
                                state?.Add(variable.Name);
                            }
                            else state?.Remove(variable.Name);
                        }
                        break;
                    case ExpressionStatement expression: Eval(expression.Expression); break;
                    case IfElseStatement conditional:
                    {
                        Eval(conditional.Condition);
                        var entry = Copy();
                        if (IsTrue(conditional.Condition)) { Exec(conditional.TrueStatement); break; }
                        Exec(conditional.TrueStatement);
                        var after = state;
                        state = entry;
                        if (conditional.FalseStatement is not null) Exec(conditional.FalseStatement);
                        state = Join(after, state);
                        break;
                    }
                    case WhileStatement loop:
                    {
                        Eval(loop.Condition);
                        var exit = IsTrue(loop.Condition) ? null : Copy();
                        Loop(loop.EmbeddedStatement, ref exit);
                        state = exit;
                        break;
                    }
                    case DoWhileStatement loop:
                    {
                        breaks.Push([]);
                        continues.Push([]);
                        Exec(loop.EmbeddedStatement);
                        foreach (var entry in continues.Pop()) state = Join(state, entry);
                        Eval(loop.Condition);
                        var exit = IsTrue(loop.Condition) ? null : Copy();
                        foreach (var entry in breaks.Pop()) exit = Join(exit, entry);
                        state = exit;
                        break;
                    }
                    case ForStatement loop:
                    {
                        foreach (var initializer in loop.Initializers) Exec(initializer);
                        if (loop.Condition is not null) Eval(loop.Condition);
                        var exit = loop.Condition is null || IsTrue(loop.Condition) ? null : Copy();
                        Loop(loop.EmbeddedStatement, ref exit, loop.Iterators);
                        state = exit;
                        break;
                    }
                    case ForeachStatement loop:
                    {
                        Eval(loop.InExpression);
                        var exit = Copy();
                        state?.Add(loop.VariableDesignation is SingleVariableDesignation single ? single.Identifier : "");
                        Loop(loop.EmbeddedStatement, ref exit);
                        state = exit;
                        break;
                    }
                    case SwitchStatement @switch:
                    {
                        Eval(@switch.Expression);
                        var entry = Copy();
                        breaks.Push([]);
                        var hasDefault = false;
                        HashSet<string>? merged = null;
                        foreach (var section in @switch.SwitchSections)
                        {
                            hasDefault |= section.CaseLabels.Any(l => l.Expression is null);
                            state = entry is null ? null : new HashSet<string>(entry);
                            foreach (var statement in section.Statements) Exec(statement);
                            merged = merged is null && state is null ? null : Join(merged, state);
                        }
                        if (!hasDefault) merged = Join(merged, entry);
                        foreach (var exit in breaks.Pop()) merged = Join(merged, exit);
                        state = merged;
                        break;
                    }
                    case BreakStatement:
                        if (breaks.Count > 0 && state is not null) breaks.Peek().Add(state);
                        state = null;
                        break;
                    case ContinueStatement:
                        if (continues.Count > 0 && state is not null) continues.Peek().Add(state);
                        state = null;
                        break;
                    case ReturnStatement @return:
                        if (@return.Expression is not null) Eval(@return.Expression);
                        Exit();
                        state = null;
                        break;
                    case ThrowStatement @throw:
                        if (@throw.Expression is not null) Eval(@throw.Expression);
                        state = null;
                        break;
                    case YieldReturnStatement yield: Eval(yield.Expression); break;
                    case YieldBreakStatement:
                        Exit();
                        state = null;
                        break;
                    case TryCatchStatement @try:
                    {
                        var entry = Copy();
                        Exec(@try.TryBlock);
                        var after = state;
                        foreach (var clause in @try.CatchClauses)
                        {
                            state = entry is null ? null : new HashSet<string>(entry);
                            if (clause.Condition is not null) Eval(clause.Condition);
                            Exec(clause.Body);
                            after = after is null && state is null ? null : Join(after, state);
                        }
                        if (@try.FinallyBlock is not null)
                        {
                            state = entry is null ? null : new HashSet<string>(entry);
                            Exec(@try.FinallyBlock);
                            if (after is not null && state is not null) after.UnionWith(state);
                            else if (state is null) after = null;
                        }
                        state = after;
                        break;
                    }
                    default:
                        foreach (var child in node.Children)
                        {
                            if (child is Expression value) Eval(value);
                            else if (child is Statement statement) Exec(statement);
                            else if (child is VariableInitializer) Exec(child);
                        }
                        break;
                }
            }

            private void Loop(Statement embedded, ref HashSet<string>? exit, IEnumerable<Statement>? iterators = null)
            {
                breaks.Push([]);
                continues.Push([]);
                Exec(embedded);
                foreach (var entry in continues.Pop()) state = Join(state, entry);
                if (iterators is not null)
                    foreach (var iterator in iterators) Exec(iterator);
                foreach (var entry in breaks.Pop()) exit = Join(exit, entry);
            }

            private static bool IsTrue(Expression condition) => condition is PrimitiveExpression { Value: true };

            private void Read(string name)
            {
                if (state is null || !tracked.Contains(name) || state.Contains(name)) return;
                if (current.TryGetValue(name, out var variable)) needsDefault.Add(variable);
                else if (outParameters.Contains(name)) outNeedsDefault.Add(name);
                state.Add(name);
            }

            private void Eval(Expression? node)
            {
                if (node is null) return;
                switch (node)
                {
                    case IdentifierExpression identifier:
                        if (identifier.Annotation<MemberResolveResult>() is null) Read(identifier.Identifier);
                        break;
                    case AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression target } assignment when target.Annotation<MemberResolveResult>() is null:
                        Eval(assignment.Right);
                        state?.Add(target.Identifier);
                        break;
                    case AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: MemberReferenceExpression { Target: IdentifierExpression target } member } assignment
                        when target.Annotation<ResolveResult>()?.Type is { IsReferenceType: false }:
                        // 结构体局部的字段写入不读这个局部，整个结构体也还没赋值。
                        Eval(assignment.Right);
                        break;
                    case DirectionExpression { FieldDirection: FieldDirection.Out, Expression: IdentifierExpression target } when target.Annotation<MemberResolveResult>() is null:
                        state?.Add(target.Identifier);
                        break;
                    case BinaryOperatorExpression { Operator: BinaryOperatorType.ConditionalAnd or BinaryOperatorType.ConditionalOr or BinaryOperatorType.NullCoalescing } binary:
                    {
                        Eval(binary.Left);
                        var after = Copy();
                        Eval(binary.Right);
                        state = after;
                        break;
                    }
                    case ConditionalExpression conditional:
                    {
                        Eval(conditional.Condition);
                        var entry = Copy();
                        Eval(conditional.TrueExpression);
                        var left = state;
                        state = entry;
                        Eval(conditional.FalseExpression);
                        state = Join(left, state);
                        break;
                    }
                    case LambdaExpression or AnonymousMethodExpression:
                    {
                        var after = Copy();
                        var savedBreaks = breaks;
                        var savedContinues = continues;
                        breaks = new();
                        continues = new();
                        foreach (var child in node.Children.Where(c => c is BlockStatement or Expression))
                        {
                            if (child is Expression value) Eval(value);
                            else Exec(child);
                        }
                        breaks = savedBreaks;
                        continues = savedContinues;
                        state = after;
                        break;
                    }
                    default:
                        foreach (var child in node.Children)
                        {
                            if (child is Expression value) Eval(value);
                            else if (child is Statement statement) Exec(statement);
                        }
                        break;
                }
            }
        }
    }
}
