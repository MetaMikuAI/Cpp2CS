using ICSharpCode.Decompiler.CSharp.Syntax;
using ICSharpCode.Decompiler.CSharp.Transforms;
using ICSharpCode.Decompiler.Semantics;
using ICSharpCode.Decompiler.TypeSystem;

namespace Cpp2CS.Output;

public static partial class Decompilation
{
    /// <summary>折叠被结构体复制隔开的枚举器初始化与标准 while/finally 枚举模式。</summary>
    private sealed class EnumeratorCopies : IAstTransform
    {
        public void Run(AstNode rootNode, TransformContext context)
        {
            foreach (var block in rootNode.Descendants.OfType<BlockStatement>().ToArray())
            {
                var statements = block.Statements.ToArray();
                for (var i = 0; i + 1 < statements.Length; i++)
                {
                    if (statements[i] is not VariableDeclarationStatement first || first.Variables.Count != 1
                        || statements[i + 1] is not VariableDeclarationStatement second || second.Variables.Count != 1
                        || first.Type.ToString() != second.Type.ToString()) continue;
                    var from = first.Variables.Single();
                    var to = second.Variables.Single();
                    if (from.Initializer is not InvocationExpression { Target: MemberReferenceExpression { MemberName: "GetEnumerator" } }
                        || to.Initializer is not IdentifierExpression id || id.Identifier != from.Name
                        || block.Descendants.OfType<IdentifierExpression>().Count(x => x.Identifier == from.Name) != 1) continue;
                    to.Initializer.ReplaceWith(from.Initializer.Clone());
                    first.Remove();
                }
                statements = block.Statements.ToArray();
                for (var i = 0; i + 1 < statements.Length; i++)
                {
                    if (statements[i] is not VariableDeclarationStatement declaration || declaration.Variables.Count != 1
                        || declaration.Variables.Single() is not { Initializer: InvocationExpression { Arguments.Count: 0,
                            Target: MemberReferenceExpression { MemberName: "GetEnumerator" } factory } } variable
                        || statements[i + 1] is not TryCatchStatement { CatchClauses.Count: 0 } guarded
                        || guarded.TryBlock.Statements.Count != 1 || guarded.TryBlock.Statements.Single() is not WhileStatement loop
                        || loop.Condition is not InvocationExpression { Arguments.Count: 0,
                            Target: MemberReferenceExpression { MemberName: "MoveNext", Target: IdentifierExpression move } } || move.Identifier != variable.Name
                        || loop.EmbeddedStatement is not BlockStatement body || body.Statements.FirstOrDefault() is not VariableDeclarationStatement current
                        || current.Variables.Count != 1 || current.Variables.Single().Initializer is not MemberReferenceExpression
                            { MemberName: "Current", Target: IdentifierExpression read } || read.Identifier != variable.Name
                        || guarded.FinallyBlock is not { } finallyBlock || finallyBlock.Statements.Count != 1 || finallyBlock.Statements.Single() is not ExpressionStatement
                            { Expression: InvocationExpression { Arguments.Count: 0, Target: MemberReferenceExpression
                                { MemberName: "Dispose", Target: IdentifierExpression dispose } } } || dispose.Identifier != variable.Name
                        || block.Descendants.OfType<IdentifierExpression>().Count(x => x.Identifier == variable.Name) != 3) continue;
                    if (variable.Initializer.Annotation<ResolveResult>()?.Type.GetAllBaseTypes()
                        .Any(t => t.FullName == "System.IDisposable") != true) continue;
                    var content = (BlockStatement)body.Clone();
                    content.Statements.First().Remove();
                    guarded.ReplaceWith(new ForeachStatement(current.Type.Clone(), new SingleVariableDesignation(current.Variables.Single().Name),
                        factory.Target.Clone(), content));
                    declaration.Remove();
                }
            }
        }
    }
}
