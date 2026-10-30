using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal sealed class ConstructionState : IStatementKeyed
{
    internal readonly Dictionary<Call, InlineConstructors.Match> inlineConstructors = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<ulong, LocalValue> mergedBoxValues = [];
    internal readonly Dictionary<Store, LocalValue> boxArgumentStores = [];
    /// <summary>对象分配 → 与之合并的构造调用；构造调用 → 分配结果变量。</summary>
    internal readonly Dictionary<Call, Variable> constructed = new(ReferenceEqualityComparer.Instance);
    /// <summary>与分配合并的基类构造调用 → 类型自己（只转调基类构造）的无参构造函数。</summary>
    internal readonly Dictionary<Call, MethodRef> forwardedConstructors = new(ReferenceEqualityComparer.Instance);
    /// <summary>装箱调用 → 写入被装箱栈槽的值。</summary>
    internal readonly Dictionary<Call, Expr> boxed = new(ReferenceEqualityComparer.Instance);
    internal readonly Dictionary<Call, DefinitionRef> delegateCreations = new(ReferenceEqualityComparer.Instance);

    public void Replace(Stmt previous, Stmt? replacement)
    {
        StatementKeys.Replace(inlineConstructors, previous, replacement);
        StatementKeys.Replace(boxArgumentStores, previous, replacement);
        StatementKeys.Replace(constructed, previous, replacement);
        StatementKeys.Replace(forwardedConstructors, previous, replacement);
        StatementKeys.Replace(boxed, previous, replacement);
        StatementKeys.Replace(delegateCreations, previous, replacement);
    }
}
