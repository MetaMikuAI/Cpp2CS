using ICSharpCode.Decompiler.CSharp;
using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>
    /// 不捕获的 lambda 由编译器缓存在静态字段：cache ?? (cache = lambda)。clang 把读缓存、判空和写缓存分散到不同的块并按路径复制，反编译器认不出，缓存字段留在源码里。
    /// 读缓存和写缓存都换成 lambda 本身，C# 编译器会重新生成缓存。之后只被赋过 lambda 的局部不为空，判空折叠，死分支和死语句删去，只读一次的局部代回读取处。
    /// 差别只在委托对象是否为同一个实例（委托按方法和目标比较相等），lambda 没有副作用。
    /// </summary>
    private sealed class CachedLambdas : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var body in rootNode.Descendants.OfType<BlockStatement>().Where(b => b.Parent is EntityDeclaration).ToArray())
                Rewrite(body);
        }

        private static IField? Cache(AstNode node) => node.GetSymbol() is IField field && field.Name.StartsWith("<>9__", StringComparison.Ordinal) ? field : null;

        /// <summary>缓存的委托值：lambda，或单例 &lt;&gt;c.&lt;&gt;9 上的方法组。别的接收者会被改写，读取不能挪动。</summary>
        private static bool IsDelegateValue(AstNode? value) =>
            value is LambdaExpression or AnonymousMethodExpression || value is MemberReferenceExpression { Target: var receiver } && value.GetSymbol() is IMethod && receiver.GetSymbol() is IField { IsStatic: true, Name: "<>9" };

        private static void Rewrite(BlockStatement body)
        {
            var values = new Dictionary<IField, Expression>();
            foreach (var write in body.Descendants.OfType<AssignmentExpression>())
                if (write.Operator == AssignmentOperatorType.Assign && Cache(write.Left) is { } field && IsDelegateValue(write.Right)) values.TryAdd(field, write.Right);
            if (values.Count == 0) return;
            // 先换读缓存，再换写缓存：写缓存的左边不算读。
            foreach (var read in body.Descendants.OfType<Expression>().Where(e => e is MemberReferenceExpression or IdentifierExpression).ToArray())
                if (Cache(read) is { } field && values.TryGetValue(field, out var value) && !(read.Parent is AssignmentExpression { Operator: AssignmentOperatorType.Assign } a && a.Left == read))
                    read.ReplaceWith(value.Clone());
            foreach (var write in body.Descendants.OfType<AssignmentExpression>().ToArray())
            {
                if (write.Operator != AssignmentOperatorType.Assign || Cache(write.Left) is null) continue;
                if (write.Parent is ExpressionStatement statement) statement.Remove();
                else if (IsDelegateValue(write.Right)) write.ReplaceWith(write.Right.Clone());
            }
            FoldLocals(body);
        }

        private static IEnumerable<string> Candidates(BlockStatement body) =>
            body.Descendants.OfType<VariableInitializer>().Where(v => v.Parent is VariableDeclarationStatement && IsDelegateValue(v.Initializer)).Select(v => v.Name)
                .Concat(body.Descendants.OfType<AssignmentExpression>().Where(a => a.Left is IdentifierExpression && IsDelegateValue(a.Right)).Select(a => ((IdentifierExpression)a.Left).Identifier)).Distinct();

        /// <summary>局部的每次赋值都是委托值，取地址或传引用时不算。</summary>
        private static void FoldLocals(BlockStatement body)
        {
            foreach (var name in Candidates(body).ToArray())
            {
                var uses = body.Descendants.OfType<IdentifierExpression>().Where(i => i.Identifier == name).ToArray();
                var writes = uses.Where(i => i.Parent is AssignmentExpression a && a.Left == i).Select(i => (AssignmentExpression)i.Parent!).ToArray();
                var declaration = body.Descendants.OfType<VariableInitializer>().FirstOrDefault(v => v.Name == name && v.Parent is VariableDeclarationStatement);
                if (declaration is null || !writes.All(w => w.Operator == AssignmentOperatorType.Assign && IsDelegateValue(w.Right))) continue;
                if (uses.Any(i => i.Parent is DirectionExpression || i.Ancestors.Any(n => n is LambdaExpression or AnonymousMethodExpression))) continue;
                if (declaration.Initializer is { } initial && initial.ToString().Length > 0 && !IsDelegateValue(initial)) continue;
                foreach (var test in uses.Select(i => i.Parent).OfType<BinaryOperatorExpression>().Where(b => b.Right is NullReferenceExpression && b.Operator is BinaryOperatorType.Equality or BinaryOperatorType.InEquality).ToArray())
                    if (test.Parent is not null) Fold(test, test.Operator == BinaryOperatorType.InEquality);
                Inline(body, name);
            }
        }

        private static void Fold(BinaryOperatorExpression test, bool truth)
        {
            switch (test.Parent)
            {
                case ConditionalExpression conditional when conditional.Condition == test:
                    conditional.ReplaceWith((truth ? conditional.TrueExpression : conditional.FalseExpression).Clone());
                    break;
                case IfElseStatement branch when branch.Condition == test:
                    Choose(branch, truth ? branch.TrueStatement : branch.FalseStatement);
                    break;
            }
        }

        /// <summary>if 换成选中的分支；分支以跳转结尾时，同一块里后面到下一个标签之前都不可达。</summary>
        private static void Choose(IfElseStatement branch, Statement? chosen)
        {
            if (branch.Parent is not BlockStatement block)
            {
                if (chosen is not null) branch.ReplaceWith(chosen.Clone());
                else branch.ReplaceWith(new BlockStatement());
                return;
            }
            var moved = chosen is BlockStatement inner ? inner.Statements.Select(s => s.Clone()).ToArray() : chosen is null ? [] : [chosen.Clone()];
            foreach (var statement in moved) block.Statements.InsertBefore(branch, statement);
            var next = branch.NextSibling;
            branch.Remove();
            if (moved.LastOrDefault() is not (ReturnStatement or ThrowStatement or BreakStatement or ContinueStatement or GotoStatement)) return;
            while (next is not null and not LabelStatement)
            {
                var following = next.NextSibling;
                if (next is Statement and not LocalFunctionDeclarationStatement) next.Remove();
                next = following;
            }
        }

        /// <summary>只写一次、读一次或没有读的局部代回读取处，lambda 的位置没有副作用。</summary>
        private static void Inline(BlockStatement body, string name)
        {
            var uses = body.Descendants.OfType<IdentifierExpression>().Where(i => i.Identifier == name).ToArray();
            var writes = uses.Where(i => i.Parent is AssignmentExpression a && a.Left == i).Select(i => (AssignmentExpression)i.Parent!).ToArray();
            var reads = uses.Except(writes.Select(w => (IdentifierExpression)w.Left)).ToArray();
            var declaration = body.Descendants.OfType<VariableInitializer>().FirstOrDefault(v => v.Name == name && v.Parent is VariableDeclarationStatement);
            if (declaration?.Parent is not VariableDeclarationStatement { Variables.Count: 1 } statement) return;
            var initial = IsDelegateValue(declaration.Initializer) ? declaration.Initializer : null;
            if (writes.Any(w => w.Parent is not ExpressionStatement) || (initial is null ? 0 : 1) + writes.Length != 1 && reads.Length > 0) return;
            if (reads.Length > 1) return;
            // lambda 捕获的局部要在读取处仍然可见。
            if (reads.Length == 1 && writes is [var only] && !reads[0].Ancestors.Contains(only.Parent!.Parent)) return;
            var value = initial ?? writes.FirstOrDefault()?.Right;
            if (reads.Length == 1 && value is not null) reads[0].ReplaceWith(value.Clone());
            foreach (var write in writes) write.Parent!.Remove();
            statement.Remove();
        }
    }
}
