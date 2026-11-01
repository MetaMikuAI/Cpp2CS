using Cpp2CS.Machine.Algebra;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery;

/// <summary>异常布局排好之后，异常片段的语句区间随插入与删除移动（插入点之后的端点后移，删除点之后的端点前移）。</summary>
internal sealed class FragmentPositions(MethodSession session) : IStatementPositions
{
    public void Inserted(Block block, int index)
    {
        foreach (var fragment in Fragments(block))
        {
            if (fragment.First > index) fragment.First++;
            if (fragment.Limit > index) fragment.Limit++;
        }
    }

    public void Removed(Block block, int index)
    {
        foreach (var fragment in Fragments(block))
        {
            if (fragment.First > index) fragment.First--;
            if (fragment.Limit > index) fragment.Limit--;
        }
    }

    private IEnumerable<ExceptionFragment> Fragments(Block block) =>
        session.Analysis.ArrangedFragments()?.Where(f => f.Block == block) ?? [];
}
