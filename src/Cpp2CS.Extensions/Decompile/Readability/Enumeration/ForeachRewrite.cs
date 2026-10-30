using ICSharpCode.Decompiler.CSharp.Syntax;

namespace Cpp2CS.Extensions.Decompile;

/// <summary>路径与清理已经证明的循环；只保存生成 foreach 所需的稳定输入。</summary>
internal sealed record EnumerationLoop(AstType ElementType, string ElementName, Expression Collection, BlockStatement Body)
{
    public ForeachStatement Materialize() => new(ElementType.Clone(), new SingleVariableDesignation(ElementName), Collection.Clone(), Body);
}

/// <summary>候选的 AST 修改集中提交；识别阶段不修改原循环的声明、出口或清理。</summary>
internal sealed class ForeachRewrite(Statement original, EnumerationLoop candidate)
{
    public ForeachStatement Loop { get; } = candidate.Materialize();
    public List<Statement> Prefix { get; } = [];
    public List<Statement> Suffix { get; } = [];
    public List<Statement> Removed { get; } = [];
    public List<(VariableInitializer Variable, Expression Value)> Initializers { get; } = [];

    public void Commit()
    {
        if (original.Parent is not BlockStatement parent || Loop.Parent is not null)
            throw new InvalidOperationException("foreach 候选的替换位置已改变");
        foreach (var (variable, value) in Initializers) variable.Initializer = value.Clone();
        if (Prefix.Count == 0)
        {
            original.ReplaceWith(Loop);
            Statement previous = Loop;
            foreach (var statement in Suffix)
            {
                parent.Statements.InsertAfter(previous, statement);
                previous = statement;
            }
        }
        else
        {
            var block = new BlockStatement();
            foreach (var statement in Prefix) block.Statements.Add(statement);
            block.Statements.Add(Loop);
            foreach (var statement in Suffix) block.Statements.Add(statement);
            original.ReplaceWith(block);
        }
        foreach (var statement in Removed.Distinct()) statement.Remove();
    }
}
