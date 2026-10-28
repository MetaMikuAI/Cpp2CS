using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Cpp2CS.Output;

internal sealed partial class RecoveredForeach
{
    private sealed record SplitCleanup(IfElseStatement Original, IfElseStatement View, Statement Normal, VariableDeclarationStatement Declaration,
        TryCatchStatement[] Guards, (LabelStatement Before, Statement Cleanup, LabelStatement After)[] Exits);

    // 两个互斥遍历共用清理时，先为各分支建立独立匹配视图；必须同时折叠。
    private static List<SplitCleanup> NormalizeSplitCleanup(AstNode root)
    {
        var changed = new List<SplitCleanup>();
        foreach (var choice in root.Descendants.OfType<IfElseStatement>().Reverse().ToArray())
        {
            if (choice.Parent is not BlockStatement parent || choice.TrueStatement is not BlockStatement positive
                || choice.FalseStatement is not BlockStatement negative
                || choice.Ancestors.FirstOrDefault(n => n is MethodDeclaration) is not MethodDeclaration method) continue;
            var siblings = parent.Statements.ToArray(); var index = Array.IndexOf(siblings, choice);
            if (index + 1 >= siblings.Length) continue;
            var branches = new[] { positive, negative };
            var loops = new List<BlockStatement>();
            string? name = null;
            foreach (var branch in branches)
            {
                if (branch.Statements.ToArray() is not [ExpressionStatement { Expression: AssignmentExpression
                        { Operator: AssignmentOperatorType.Assign, Left: IdentifierExpression target,
                            Right: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression { MemberName: "GetEnumerator" } } factory } },
                        TryCatchStatement { FinallyBlock: null } guarded]
                    || name is not null && name != target.Identifier || !Enumerator(factory).Disposable || Enumerator(factory).Reference != false
                    || guarded.CatchClauses.ToArray() is not [var catcher] || catcher.Condition is not null
                    || catcher.Type?.ToString() is not ("Exception" or "System.Exception") || !ConditionalCleanup(catcher, target.Identifier)
                    || guarded.TryBlock?.Statements.ToArray() is not [WhileStatement { Condition: InvocationExpression { Arguments.Count: 0,
                        Target: MemberReferenceExpression { MemberName: "MoveNext", Target: var receiver } }, EmbeddedStatement: BlockStatement body }]
                    || !Name(receiver, target.Identifier)) break;
                name = target.Identifier; loops.Add(body);
            }
            if (loops.Count != 2 || !Dispose(siblings[index + 1], name!)) continue;
            if (method.Descendants.OfType<VariableDeclarationStatement>().Where(d => d.Variables.Any(v => v.Name == name)).ToArray()
                is not [var declaration] || declaration.Variables.ToArray() is not [{ Initializer: DefaultValueExpression }]) continue;
            var jumps = loops.SelectMany(body => body.Descendants.OfType<GotoStatement>().Where(j => j.Label is null
                || !body.Descendants.OfType<LabelStatement>().Any(l => l.Label == j.Label))).ToArray();
            var exits = new List<(LabelStatement Before, Statement Cleanup, LabelStatement After)>();
            var names = method.Descendants.OfType<LabelStatement>().Select(l => l.Label).ToHashSet();
            string Label(string stem)
            {
                var candidate = stem;
                for (var suffix = 2; !names.Add(candidate); suffix++) candidate = stem + suffix;
                return candidate;
            }
            var valid = true;
            foreach (var group in jumps.GroupBy(j => j.Label))
            {
                if (group.Key is null || method.Descendants.OfType<LabelStatement>().Where(l => l.Label == group.Key).ToArray() is not [var label]
                    || label.Parent is not BlockStatement destination
                    || method.Descendants.OfType<GotoStatement>().Any(j => j.Label == group.Key && !jumps.Contains(j))) { valid = false; break; }
                AstNode anchor = choice;
                while (anchor.Parent != destination && anchor.Parent is BlockStatement or IfElseStatement) anchor = anchor.Parent;
                var tail = destination.Statements.ToArray(); var position = Array.IndexOf(tail, label);
                if (anchor.Parent != destination || position == 0 || position + 1 >= tail.Length
                    || tail[position - 1] is not (ReturnStatement or GotoStatement or ThrowStatement)
                    || !Dispose(tail[position + 1], name!)) { valid = false; break; }
                exits.Add((label, tail[position + 1], new LabelStatement(Label("enumerationExit"))));
            }
            if (!valid) continue;
            var allowed = choice.Descendants.Concat(siblings[index + 1].Descendants)
                .Concat(exits.SelectMany(e => e.Cleanup.Descendants)).ToHashSet();
            if (method.Descendants.OfType<IdentifierExpression>().Any(id => id.Identifier == name && !allowed.Contains(id))) continue;
            var variables = method.Descendants.OfType<IdentifierExpression>().Select(id => id.Identifier)
                .Concat(method.Descendants.OfType<VariableInitializer>().Select(v => v.Name))
                .Concat(method.Descendants.OfType<ParameterDeclaration>().Select(p => p.Name)).ToHashSet();
            var view = (IfElseStatement)choice.Clone();
            var views = new[] { (BlockStatement)view.TrueStatement, (BlockStatement)view.FalseStatement! };
            var guards = views.Select(b => b.Statements.OfType<TryCatchStatement>().Single()).ToArray();
            for (var i = 0; i < views.Length; i++)
            {
                var branch = views[i];
                branch.Statements.Add(siblings[index + 1].Clone());
                var localJumps = guards[i].TryBlock!.Descendants.OfType<GotoStatement>().Where(j => exits.Any(e => e.Before.Label == j.Label)).ToArray();
                var done = Label("enumerationContinue");
                if (localJumps.Length != 0) branch.Statements.Add(new GotoStatement(done));
                foreach (var group in localJumps.GroupBy(j => j.Label))
                {
                    var exit = exits.Single(e => e.Before.Label == group.Key);
                    var local = Label("enumerationMatch");
                    foreach (var jump in group) jump.Label = local;
                    branch.Statements.Add(new LabelStatement(local));
                    branch.Statements.Add(exit.Cleanup.Clone());
                    branch.Statements.Add(new GotoStatement(exit.After.Label));
                }
                if (localJumps.Length != 0) { branch.Statements.Add(new LabelStatement(done)); branch.Statements.Add(new EmptyStatement()); }
                var localName = name + "Branch";
                for (var suffix = 2; !variables.Add(localName); suffix++) localName = name + "Branch" + suffix;
                foreach (var use in branch.Descendants.OfType<IdentifierExpression>().Where(id => id.Identifier == name)) use.Identifier = localName;
                var localDeclaration = (VariableDeclarationStatement)declaration.Clone();
                localDeclaration.Variables.Single().Name = localName;
                branch.Statements.InsertBefore(branch.Statements.First(), localDeclaration);
            }
            choice.ReplaceWith(view); siblings[index + 1].Remove();
            foreach (var exit in exits)
            {
                ((BlockStatement)exit.Before.Parent!).Statements.InsertAfter(exit.Cleanup, exit.After);
                exit.Cleanup.Remove();
            }
            changed.Add(new(choice, view, siblings[index + 1], declaration, guards, exits.ToArray()));
        }
        return changed;
    }

    private static void RestoreSplitCleanup(AstNode root, IEnumerable<SplitCleanup> changes)
    {
        foreach (var change in changes)
        {
            if (!change.Guards.Any(g => root.Descendants.Contains(g))) { change.Declaration.Remove(); continue; }
            if (change.View.Parent is not BlockStatement parent) continue;
            change.View.ReplaceWith(change.Original); parent.Statements.InsertAfter(change.Original, change.Normal);
            foreach (var exit in change.Exits)
            {
                ((BlockStatement)exit.Before.Parent!).Statements.InsertAfter(exit.Before, exit.Cleanup);
                exit.After.Remove();
            }
        }
    }
}
