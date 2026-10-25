using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Typing;

/// <summary>入口寄存器（版本 0）的类型就是签名中对应参数的类型（ManagedAbi 的分类）。</summary>
public sealed class EntryArgumentContributor : ITypeContributor
{
    public string Name => "参数";

    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var (storage, type) in context.EntryTypes)
            constraints.Defines(new Variable(storage, 0), type, new(Name, context.Function.EntryBlock.Start, $"{storage} : {type}"));
    }
}

/// <summary>
/// φ 的值来自各前驱的来源变量：每个来源流向目标。版本为负的来源是调用破坏后的未定义值（SsaBuilder 的约定），
/// 它没有值，不能由 φ 目标的使用反推出类型。
/// </summary>
public sealed class PhiContributor : ITypeContributor
{
    public string Name => "汇合";

    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var phi in context.Statements.OfType<Phi>())
            foreach (var source in phi.Sources)
            {
                constraints.Flows(source, phi.Target, new(Name, phi.Address, $"{source} → {phi.Target}"));
                if (source.Version < 0) constraints.IsClobbered(source, new(Name, phi.Address, $"{source} 被调用破坏"));
            }
    }
}

/// <summary>同宽的复制 <c>v = u</c>：u 的值流向 v。</summary>
public sealed class CopyContributor : ITypeContributor
{
    public string Name => "复制";

    public void Contribute(TypingContext context, TypeConstraints constraints)
    {
        foreach (var define in context.Statements.OfType<Define>())
            if (define.Value is Use use && use.Width == define.Target.Width)
                constraints.Flows(use.Variable, define.Target, new(Name, define.Address, $"{use.Variable} → {define.Target}"));
    }
}
