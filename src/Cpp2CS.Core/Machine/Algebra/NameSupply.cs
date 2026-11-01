
namespace Cpp2CS.Machine.Algebra;

/// <summary>每方法的合成编号；保留各用途既有编号区间。</summary>
internal sealed class NameSupply(int first, int step = 1)
{
    private int next = first;
    public int Next() { var value = next; next += step; return value; }
    public const ulong JoinedEdgeBase = 1UL << 62;
    public const ulong EntryLabel = 0xf400000000000000UL;
    public const ulong ExceptionLabelBase = 0xf500000000000000UL;
    public const ulong ExceptionGuardBase = 0xf700000000000000UL;
}
