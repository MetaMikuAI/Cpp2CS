using Cpp2CS.Kernel.Engine;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel;

/// <summary>
/// 唯一的证明入口（设计 9.3）：给定一条声明，返回凭据或反驳。五项义务：
///   合法——操作能在本方法里合法写出：目录项的变体与元数据相符，操作数的个数与位宽相符，成员可访问；
///   去向——被占用的可能抛出的效果与落点的异常处理目标相同；
///   覆盖、对应、搬移——由共同执行沿路径核对（见 <see cref="CoExecution"/>）。
/// 引擎不知道声明来自哪个发现器，也不按操作的种类分支。
/// </summary>
public static class Proof
{
    public static ProofOutcome Prove(RecoveryContext context, Claim claim, int budget = 200_000)
    {
        var snapshot = context.Snapshot;
        ProofOutcome Refute(RefutationLayer layer, Obligation? obligation, string detail) =>
            new(claim, null, new Refutation(layer, obligation, detail), [], 0, 0);

        foreach (var operand in claim.Operands)
            if (!snapshot.Terms.Owns(operand)) return Refute(RefutationLayer.Explanation, Obligation.Legality, "操作数不是这张快照的项");
        if (claim.Landing.Block.Index < 0 || claim.Landing.Block.Index >= snapshot.BlockCount
            || claim.Landing.Index < 0 || claim.Landing.Index > snapshot.OccurrenceCount(claim.Landing.Block))
            return Refute(RefutationLayer.Explanation, Obligation.Coverage, "落点不是这张快照的程序点");

        // 合法：模板由内核按目录与元数据取；取不出来，或声明与目录项不符，这个操作就写不出来。
        ClaimTemplate template;
        try
        {
            template = ClaimTemplate.Build(claim, context.Metadata, snapshot.Terms, snapshot.PointerBits);
        }
        catch (ExpansionException failure)
        {
            return Refute(RefutationLayer.Catalog, null, failure.Message);
        }
        catch (ClaimFormatException failure)
        {
            return Refute(RefutationLayer.Explanation, Obligation.Legality, failure.Message);
        }
        if (claim.Entity is { Kind: EntityKind.Field or EntityKind.Method } member && !context.Metadata.Accessible(member, context.Host.DeclaringType))
            return Refute(RefutationLayer.Explanation, Obligation.Legality, $"{member} 在本方法所属的类里不可访问");
        if (claim.Entity is { Kind: EntityKind.Method } callee
            && CallLegality.Check(claim.Operation, callee, claim.Operands.Length > 0 && ReferenceEquals(claim.Operands[0], CallLegality.HostThis(snapshot, context.Host)),
                context.Host.Entity, context.Metadata) is { } illegal)
            return Refute(RefutationLayer.Explanation, Obligation.Legality, illegal);

        // 去向：快照里没有带展开出口的调用时，方法里没有异常处理区域，一切抛出都去往调用者。
        // 有展开出口时需要异常区域的模型（设计第 18 节）给出每个程序点的处理目标；它尚未建立，不能证明相同。
        foreach (var block in snapshot.Blocks)
            if (block.Terminator.Kind == TerminatorKind.Invoke)
                return Refute(RefutationLayer.Explanation, Obligation.Destination,
                    $"B{block.Id.Index} 是带展开出口的调用：落点与被占用效果的处理目标不能证明相同（异常区域的模型尚未建立）");

        // 覆盖、对应、搬移：先只用声明自己占用的检查确立的条件；不成立再并入其他分支确立的条件，并把它们记为依赖。
        var first = CoExecution.ProveClaim(context, claim, template, ownOnly: true, budget);
        if (first.Certificate is not null || first.Refutation!.Layer != RefutationLayer.Explanation) return first;
        var second = CoExecution.ProveClaim(context, claim, template, ownOnly: false, budget);
        return second with { Rows = [.. first.Rows.Union(second.Rows).Order(StringComparer.Ordinal)], Paths = first.Paths + second.Paths, Steps = first.Steps + second.Steps };
    }
}
