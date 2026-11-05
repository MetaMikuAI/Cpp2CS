using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 在声明局部之前整理 goto。结构恢复放不进 if 和循环的跳转会写成 goto，其中不少只差一步：
    /// 下一条就是目标；目标在循环之后；目标只有这一个入口；目标是很短的出口。这些改写都不改变 C# 语义，局部随后按新位置声明。
    /// </summary>
    private sealed class GotoCleanup : IAstTransform
    {
        private const int Rounds = 8;
        /// <summary>复制到各入口的短出口的大小上限（语法节点数）。</summary>
        private const int ShortExit = 16;

        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var scope in rootNode.DescendantsAndSelf.Where(IsFunctionBody).OfType<BlockStatement>().ToArray())
                for (var round = 0; round < Rounds; round++)
                {
                    var labels = Own(scope).OfType<LabelStatement>().GroupBy(l => l.Label).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
                    if (labels.Count == 0) break;
                    var changed = RemoveFallthroughs(scope) | InlineSingleEntries(scope, labels) | CopyShortExits(scope, labels) | RemoveUnusedLabels(scope, labels);
                    SimplifyEmptyBranches(scope);
                    if (!changed) break;
                }
        }

        private static bool IsFunctionBody(AstNode node) => node is BlockStatement && node.Parent is EntityDeclaration or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement;

        /// <summary>这个函数自身的节点：lambda 和局部函数各有自己的标签。</summary>
        private static IEnumerable<AstNode> Own(BlockStatement scope) =>
            scope.DescendantNodes(n => n is not (LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement));

        private static Statement? Next(AstNode node)
        {
            for (var sibling = node.NextSibling; sibling is not null; sibling = sibling.NextSibling)
                if (sibling is Statement statement) return statement;
            return null;
        }

        private static Statement? Previous(AstNode node)
        {
            for (var sibling = node.PrevSibling; sibling is not null; sibling = sibling.PrevSibling)
                if (sibling is Statement statement) return statement;
            return null;
        }

        /// <summary>语句正常结束后，控制是否到达 label：沿块的末尾向外走，只穿过结束后落到下一条语句的结构。</summary>
        private static bool Reaches(Statement statement, string label)
        {
            for (AstNode current = statement; ;)
            {
                if (current.Parent is BlockStatement && Next(current) is { } next)
                {
                    for (Statement? at = next; at is LabelStatement mark; at = Next(mark))
                        if (mark.Label == label) return true;
                    return false;
                }
                switch (current.Parent)
                {
                    case IfElseStatement branch:
                        current = branch;
                        break;
                    case BlockStatement block:
                        switch (block.Parent)
                        {
                            case BlockStatement:
                                current = block;
                                break;
                            case IfElseStatement or UsingStatement or LockStatement or FixedStatement or CheckedStatement or UncheckedStatement or UnsafeStatement:
                                current = block.Parent;
                                break;
                            case TryCatchStatement t when block == t.TryBlock && t.FinallyBlock is null:
                                current = t;
                                break;
                            case CatchClause { Parent: TryCatchStatement t } when t.FinallyBlock is null:
                                current = t;
                                break;
                            default:
                                return false;
                        }
                        break;
                    default:
                        return false;
                }
            }
        }

        private static bool RemoveFallthroughs(BlockStatement scope)
        {
            var changed = false;
            foreach (var jump in Own(scope).OfType<GotoStatement>().ToArray())
            {
                if (jump.Label is not { } label) continue;
                if (Reaches(jump, label)) { jump.Remove(); changed = true; continue; }
                // 目标紧跟在最近的循环或 switch 之后：这就是 break。
                if (Breakable(jump) is { } breakable && Reaches(breakable, label))
                {
                    jump.ReplaceWith(new BreakStatement());
                    changed = true;
                }
            }
            return changed;
        }

        private static Statement? Breakable(AstNode node)
        {
            for (var at = node.Parent; at is not null and not BlockStatement { Parent: EntityDeclaration or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement }; at = at.Parent)
                if (at is WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement) return (Statement)at;
            return null;
        }

        /// <summary>语句结束后控制是否可能落到下一条。</summary>
        private static bool Completes(Statement? statement) => statement switch
        {
            null => true,
            ReturnStatement or ThrowStatement or GotoStatement or BreakStatement or ContinueStatement => false,
            BlockStatement block => Completes(block.Statements.LastOrDefault()),
            IfElseStatement branch => branch.FalseStatement is null || Completes(branch.TrueStatement) || Completes(branch.FalseStatement),
            TryCatchStatement t => Completes(t.TryBlock) || t.CatchClauses.Any(c => Completes(c.Body)),
            WhileStatement { Condition: PrimitiveExpression { Value: true } } loop => FreeJumps(loop.EmbeddedStatement).OfType<BreakStatement>().Any(),
            _ => true,
        };

        /// <summary>语句中不属于内层循环或 switch 的 break、continue。</summary>
        private static IEnumerable<Statement> FreeJumps(AstNode root)
        {
            foreach (var node in root.DescendantNodesAndSelf(n => n is not (WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement or LambdaExpression or AnonymousMethodExpression or LocalFunctionDeclarationStatement) || n == root))
                if (node is BreakStatement or ContinueStatement) yield return (Statement)node;
        }

        /// <summary>从跳转走到标签所在的块：把目标的语句移到跳转处，途中经过的结构决定是否成立。</summary>
        private static (bool EntersTry, bool EntersBreakable, bool Blocked) Path(AstNode jump, BlockStatement target)
        {
            var (entersTry, entersBreakable, blocked) = (false, false, false);
            for (var at = jump.Parent; at is not null && at != target; at = at.Parent)
                switch (at)
                {
                    case BlockStatement { Parent: TryCatchStatement t } block when block == t.TryBlock: entersTry = true; if (t.FinallyBlock is not null) blocked = true; break;
                    case BlockStatement { Parent: TryCatchStatement t } block when block == t.FinallyBlock: blocked = true; break;
                    case CatchClause { Parent: TryCatchStatement t }: if (t.FinallyBlock is not null) blocked = true; break;
                    case WhileStatement or DoWhileStatement or ForStatement or ForeachStatement or SwitchStatement: entersBreakable = true; break;
                    case UsingStatement or LockStatement or FixedStatement or CheckedStatement or UncheckedStatement: blocked = true; break;
                }
            return (entersTry, entersBreakable, blocked);
        }

        /// <summary>标签之后到下一个标签或块尾的语句。</summary>
        private static List<Statement> Segment(LabelStatement label)
        {
            var segment = new List<Statement>();
            for (var at = Next(label); at is not null and not LabelStatement; at = Next(at)) segment.Add(at);
            return segment;
        }

        /// <summary>把跳转换成这些语句。跳转可以是 if 的直接子语句，这时要包一层块。</summary>
        private static void Replace(Statement jump, IEnumerable<Statement> statements)
        {
            var list = jump.Parent switch { BlockStatement block => block.Statements, SwitchSection section => section.Statements, _ => null };
            if (list is null)
            {
                var wrapper = new BlockStatement();
                jump.ReplaceWith(wrapper);
                foreach (var statement in statements) wrapper.Add(statement);
                return;
            }
            foreach (var statement in statements) list.InsertBefore(jump, statement);
            jump.Remove();
        }

        /// <summary>目标只有一个入口且不会从上方落入：把它移到跳转处。移进 try 会让处理块接住它的异常，所以不跨 try。</summary>
        private static bool InlineSingleEntries(BlockStatement scope, Dictionary<string, LabelStatement> labels)
        {
            var changed = false;
            foreach (var jumps in Own(scope).OfType<GotoStatement>().Where(g => g.Label is not null).GroupBy(g => g.Label!).ToArray())
            {
                if (jumps.Count() != 1 || !labels.TryGetValue(jumps.Key, out var label) || label.Parent is not BlockStatement home) continue;
                var jump = jumps.Single();
                if (jump.Parent is null || Previous(label) is not { } previous || Completes(previous)) continue;
                var segment = Segment(label);
                if (segment.Count == 0 || Completes(segment[^1]) || segment.Any(s => s == jump || s.Descendants.Contains(jump))) continue;
                var (entersTry, entersBreakable, blocked) = Path(jump, home);
                if (entersTry || blocked || !jump.Ancestors.Contains(home)) continue;
                if (entersBreakable && segment.Any(s => FreeJumps(s).Any())) continue;
                foreach (var statement in segment) statement.Remove();
                Replace(jump, segment);
                label.Remove();
                labels.Remove(jumps.Key);
                changed = true;
            }
            return changed;
        }

        /// <summary>不抛出、没有效果的出口可以复制进 try；其他出口复制进 try 后，异常会被处理块接住。</summary>
        private static bool Simple(Expression? expression) => expression is null or IdentifierExpression or PrimitiveExpression or NullReferenceExpression or ThisReferenceExpression or DefaultValueExpression;

        private static bool NoThrow(Statement statement) => statement switch
        {
            ReturnStatement r => Simple(r.Expression),
            GotoStatement => true,
            ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression, Right: var right } } => Simple(right),
            _ => false,
        };

        private static bool CopyShortExits(BlockStatement scope, Dictionary<string, LabelStatement> labels)
        {
            var changed = false;
            var jumps = Own(scope).OfType<GotoStatement>().Where(g => g.Label is not null).ToLookup(g => g.Label!);
            foreach (var label in labels.Values)
            {
                if (!jumps.Contains(label.Label) || label.Parent is not BlockStatement home) continue;
                var segment = Segment(label);
                if (segment.Count is 0 or > 2 || segment[^1] is not (ReturnStatement or ThrowStatement or GotoStatement)) continue;
                if (segment.Count == 2 && segment[0] is not ExpressionStatement { Expression: AssignmentExpression { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression } }) continue;
                if (segment.Sum(s => s.DescendantsAndSelf.Count()) > ShortExit) continue;
                foreach (var jump in jumps[label.Label])
                {
                    if (jump.Parent is null || segment.Any(s => s == jump || s.Descendants.Contains(jump)) || !jump.Ancestors.Contains(home)) continue;
                    var (entersTry, _, blocked) = Path(jump, home);
                    if (blocked || entersTry && !segment.All(NoThrow)) continue;
                    Replace(jump, segment.Select(s => s.Clone()).ToArray());
                    changed = true;
                }
            }
            return changed;
        }

        /// <summary>没有入口的标签删去；上方不会落入时，它引出的语句也不可达。</summary>
        private static bool RemoveUnusedLabels(BlockStatement scope, Dictionary<string, LabelStatement> labels)
        {
            var changed = false;
            var used = Own(scope).OfType<GotoStatement>().Select(g => g.Label).OfType<string>().ToHashSet();
            foreach (var (name, label) in labels.ToArray())
            {
                if (used.Contains(name) || label.Parent is null) continue;
                if (Previous(label) is { } previous && !Completes(previous))
                    foreach (var dead in Segment(label)) dead.Remove();
                label.Remove();
                labels.Remove(name);
                changed = true;
            }
            return changed;
        }

        private static bool Pure(Expression? expression) => expression switch
        {
            IdentifierExpression or PrimitiveExpression or NullReferenceExpression or ThisReferenceExpression => true,
            UnaryOperatorExpression { Operator: UnaryOperatorType.Not } not => Pure(not.Expression),
            BinaryOperatorExpression { Operator: BinaryOperatorType.Equality or BinaryOperatorType.InEquality or BinaryOperatorType.LessThan or BinaryOperatorType.LessThanOrEqual or BinaryOperatorType.GreaterThan or BinaryOperatorType.GreaterThanOrEqual or BinaryOperatorType.ConditionalAnd or BinaryOperatorType.ConditionalOr } binary
                => Pure(binary.Left) && Pure(binary.Right),
            CastExpression cast => Pure(cast.Expression),
            _ => false,
        };

        private static T Take<T>(T node) where T : AstNode
        {
            node.Remove();
            return node;
        }

        private static Expression Negate(Expression condition) => condition switch
        {
            UnaryOperatorExpression { Operator: UnaryOperatorType.Not } not => Take(not.Expression!),
            BinaryOperatorExpression { Operator: BinaryOperatorType.Equality } equal => new BinaryOperatorExpression(Take(equal.Left!), BinaryOperatorType.InEquality, Take(equal.Right!)),
            BinaryOperatorExpression { Operator: BinaryOperatorType.InEquality } unequal => new BinaryOperatorExpression(Take(unequal.Left!), BinaryOperatorType.Equality, Take(unequal.Right!)),
            _ => new UnaryOperatorExpression(UnaryOperatorType.Not, condition),
        };

        private static bool Empty(Statement? statement) => statement is null or BlockStatement { Statements.Count: 0 };

        /// <summary>跳转删去后留下的空分支。</summary>
        private static void SimplifyEmptyBranches(BlockStatement scope)
        {
            foreach (var branch in Own(scope).OfType<IfElseStatement>().ToArray())
            {
                if (branch.Parent is null) continue;
                if (branch.FalseStatement is not null && Empty(branch.FalseStatement)) branch.FalseStatement = null;
                if (!Empty(branch.TrueStatement)) continue;
                if (branch.FalseStatement is null)
                {
                    if (Pure(branch.Condition)) branch.Remove();
                    else branch.TrueStatement ??= new BlockStatement();
                    continue;
                }
                var otherwise = Take(branch.FalseStatement);
                branch.Condition = Negate(Take(branch.Condition));
                branch.TrueStatement = otherwise;
            }
        }
    }

    /// <summary>
    /// 实现接口方法的私有方法（IL 的 .override，如状态机的 MoveNext）让 ILSpy 多写一个转发的显式实现。
    /// 同名且只有这一个目标时，合成一个公开方法：C# 的隐式实现与之等价，从外层类型调用它也能编译。
    /// </summary>
    private sealed class ForwardingImplementations : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var type in rootNode.Descendants.OfType<TypeDeclaration>().ToArray())
            {
                var methods = type.Members.OfType<MethodDeclaration>().ToArray();
                foreach (var stub in methods.Where(m => m.PrivateImplementationType is not null))
                {
                    if (stub.Body?.Statements.Where(c => c is not EmptyStatement).ToArray() is not [var only]) continue;
                    var forwarded = only switch { ExpressionStatement e => e.Expression, ReturnStatement r => r.Expression, _ => null };
                    if (forwarded is not InvocationExpression { Target: MemberReferenceExpression { Target: ThisReferenceExpression, MemberName: var name } } || name != stub.Name) continue;
                    if (methods.Where(m => m.PrivateImplementationType is null && m.Name == name).ToArray() is not [var target] || target.Parameters.Count != stub.Parameters.Count) continue;
                    target.Modifiers = target.Modifiers & ~Modifiers.VisibilityMask | Modifiers.Public;
                    stub.Remove();
                }
            }
        }
    }
}
