using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>分配专用的直线链证明；不扩大判空、类初始化等其他 Following 使用者的吸收范围。</summary>
internal static class AllocationPairing
{
    internal static IEnumerable<(Block Block, Stmt Statement)> Following(Block block, int index)
    {
        var visited = new HashSet<Block>();
        while (visited.Add(block))
        {
            for (var i = index + 1; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is Jump) break;
                yield return (block, block.Statements[i]);
            }
            // LSDA 调用点和已折叠的元数据读取可能留下无显式 Jump 的空块；唯一正常后继仍是顺序执行处。
            if (block.Statements.LastOrDefault() is not (null or Jump or Call { Kind: CallKind.Direct or CallKind.Indirect })) yield break;
            var successors = block.NormalSuccessors.ToArray();
            if (successors.Length != 1) yield break;
            var next = successors[0];
            if (next.IsLandingPad || next.Predecessors.Count(p => p.NormalSuccessors.Contains(next)) != 1) yield break;
            block = next;
            index = -1;
        }
    }

    internal static bool Uses(Stmt statement, Variable created) =>
        statement is Phi phi && phi.Sources.Contains(created)
        || ExprMap.Operands(statement).SelectMany(ExprMap.Walk).Any(e => e is Use u && u.Variable == created);

    internal static string? MotionProblem(CodeFunction range, Block source, Call allocation, Block destination,
        Call constructor, IEnumerable<Stmt> middle, Variable created)
    {
        foreach (var statement in middle)
        {
            if (Uses(statement, created)) return "构造之前分配结果已被使用";
            if (statement is Nop || statement is Define d && !ExprMap.Walk(d.Value).Any(e => e is Load or Intrinsic or Unknown)) continue;
            // NewObject 已完成相同类型的布局初始化；重复 Class::Init 不运行静态构造。
            if (statement is Call { Op.Kind: OpKind.InitClass } init && allocation.Op is { Kind: OpKind.NewObject, Operand: { } type }
                && Equals(init.Op.Operand, type)) continue;
            return "分配与构造之间有可观察操作，不能移动分配";
        }
        var first = range.ExceptionRegions.FirstOrDefault(r => r.Start <= allocation.Address && allocation.Address < r.End);
        var last = range.ExceptionRegions.FirstOrDefault(r => r.Start <= constructor.Address && constructor.Address < r.End);
        // newobj 同时承载分配（含 OOM / 类初始化）和构造的异常。两端必须有同一异常去向，
        // 相同落地点但不同 LSDA action 也不能合并；中间没有可观察操作才允许移动分配时点。
        if (source.Handler != destination.Handler || (first?.LandingPad ?? 0) != (last?.LandingPad ?? 0)
            || (first?.ActionOffset ?? 0) != (last?.ActionOffset ?? 0))
            return "分配与构造的异常去向不同，不能合并为 newobj";
        return null;
    }
}
