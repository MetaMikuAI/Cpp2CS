namespace Cpp2CS.Recovery.Values;

public sealed partial class SymTable
{
    /// <summary>按整体中的位偏移组成值。缺片保持未定义；重叠部分必须证明相同，不按枚举顺序覆盖。</summary>
    public Sym Assemble(int width, IEnumerable<(int Bit, Sym Value)> pieces)
    {
        var parts = new List<Sym>();
        var at = 0;
        foreach (var (bit, value) in pieces.OrderBy(p => p.Bit))
        {
            var start = Math.Max(0, bit);
            var end = (int)Math.Min(width, (long)bit + value.Width);
            if (end <= start) continue;
            if (start < at)
            {
                var overlap = Math.Min(at, end) - start;
                if (!ReferenceEquals(Resolve(Slice(Concat(parts), start, overlap)), Resolve(Slice(value, start - bit, overlap))))
                    return Unknown("位片 重叠来源不一致", width);
            }
            if (end <= at) continue;
            if (start > at) parts.Add(Undef(start - at));
            var from = Math.Max(at, start);
            parts.Add(Slice(value, from - bit, end - from));
            at = end;
        }
        if (at < width) parts.Add(Undef(width - at));
        return Concat(parts);
    }
}
