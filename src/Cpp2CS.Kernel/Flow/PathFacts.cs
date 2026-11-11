using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.Flow;

public enum PathTruth { Unknown, True, False }
/// <summary>Edge 非空时询问边上的事实，否则询问 Point 处的事实。</summary>
public readonly record struct PathFactKey(Point Point, Term Condition, FlowEdge? Edge = null);

/// <summary>只采用单前驱分支目标的支配事实；条件由状态查询解析，等式允许交换操作数。</summary>
public sealed class PathFactQuery(StateQueries state) : Query<PathFactKey, PathTruth>
{
    private readonly FlowQueries flow = new();
    public override Outcome<PathTruth> Compute(QueryContext c, PathFactKey key)
    {
        var index = c.Get(state.Index, 0); if (!index.IsSuccess) return index.Propagate<PathTruth>();
        var point = key.Edge is { } edge ? new Point(edge.Source, index.Value.Blocks[edge.Source].Statements.Length) : key.Point;
        if (!index.Value.Blocks.TryGetValue(point.Block, out var block) || point.Before < 0 || point.Before > block.Statements.Length)
            return Outcome<PathTruth>.Failure(new("flow.point", "程序点不属于快照。"));
        var wanted = c.Get(state.Resolve, key.Condition); if (!wanted.IsSuccess) return wanted.Propagate<PathTruth>();
        var answer = PathTruth.Unknown;
        foreach (var source in c.Snapshot.Blocks)
        {
            if (source.End is not Branch branch || branch.True == branch.False) continue;
            var condition = c.Get(state.Resolve, branch.Condition); if (!condition.IsSuccess) return condition.Propagate<PathTruth>();
            var relation = Relation(wanted.Value, condition.Value); if (relation is null) continue;
            foreach (var (target, positive) in new[] { (branch.True, true), (branch.False, false) })
            {
                bool known = key.Edge == new FlowEdge(source.Identity, target);
                if (!known && target != c.Snapshot.Entry && index.Value.Predecessors[target].Length == 1)
                {
                    var dominates = c.Get(flow.Dominates, new(target, point.Block));
                    if (!dominates.IsSuccess) return dominates.Propagate<PathTruth>();
                    known = dominates.Value;
                }
                if (!known) continue;
                var value = positive == relation.Value ? PathTruth.True : PathTruth.False;
                if (answer != PathTruth.Unknown && answer != value) return Outcome<PathTruth>.Success(PathTruth.Unknown);
                answer = value;
            }
        }
        return Outcome<PathTruth>.Success(answer);
    }
    private static (Term Term, bool Positive) Literal(Term term)
    {
        bool positive = true;
        while (term.Width == 1 && term.Operator is CoreOperator { Operation: CoreOperation.Not })
        { positive = !positive; term = term.Operands[0]; }
        if (term.Operator is CoreOperator { Operation: CoreOperation.NotEqual }) positive = !positive;
        return (term, positive);
    }
    private static bool? Relation(Term a, Term b)
    {
        var x = Literal(a); var y = Literal(b);
        bool equal = x.Term == y.Term;
        if (x.Term.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual } &&
            y.Term.Operator is CoreOperator { Operation: CoreOperation.Equal or CoreOperation.NotEqual })
            equal = (x.Term.Operands[0] == y.Term.Operands[0] && x.Term.Operands[1] == y.Term.Operands[1]) ||
                (x.Term.Operands[0] == y.Term.Operands[1] && x.Term.Operands[1] == y.Term.Operands[0]);
        return equal ? x.Positive == y.Positive : null;
    }
}
