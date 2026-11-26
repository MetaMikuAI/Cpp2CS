using Cpp2CS.Spec.Runtime;
using System.Collections.Immutable;

namespace Cpp2CS.Facts;

public sealed record RuntimeName(ImmutableArray<string> Symbols, string Basis, int Depth = 0, ulong? Parent = null, int? Offset = null)
{
    public RuntimeOperation? Operation => RuntimeOperations.BySymbol(Symbols[0]);
    public string Name => Symbols.Length == 1 ? Symbols[0] : Operation!.Id;
}
public sealed record RuntimeEdge(int Offset, ulong Target);
public sealed record RuntimeBody(ulong Address, FingerprintBody Body, RuntimeEdge[] Edges);

/// <summary>同体是有序、带边标号的图上的最大不动点。只发布双向唯一且对边封闭的配对。</summary>
public sealed class RuntimeNaming
{
    private readonly Dictionary<ulong, RuntimeName> names = [];
    public IReadOnlyDictionary<ulong, RuntimeName> Names => names;
    public bool Admitted { get; private set; }
    public string Admission { get; private set; } = "";

    /// <summary>返回查找参照行的符号键。多名行只按已登记的操作组发布，保留全部成员。</summary>
    public static string? NameOf(string[] names)
    {
        if (names.Length == 1) return names[0];
        if (names.Length == 0 || RuntimeOperations.BySymbol(names[0]) is not { } op) return null;
        return names.All(n => RuntimeOperations.BySymbol(n) == op) ? names.Order(StringComparer.Ordinal).First() : null;
    }

    private sealed record Node(string Label, int[] Children);

    public RuntimeNaming(RuntimeFingerprint reference, RuntimeBody[] image, IReadOnlyDictionary<ulong, string[]> symbols,
        IReadOnlySet<ulong> registered, IReadOnlySet<ulong> managed, string? target)
    {
        foreach (var (address, aliases) in symbols)
            if (!managed.Contains(address) && NameOf(aliases) != null) names[address] = new([.. aliases], "符号");
        if (reference.Target != target) { Admission = $"目标不符 {reference.Target} / {target ?? "未知"}，整表拒用"; return; }
        var rows = reference.Rows;
        var refByName = rows.SelectMany((row, i) => row.Names.Select(n => (n, i))).ToLookup(p => p.n, p => p.i);
        int Ref(string? name) => name != null && refByName[name].Count() == 1 ? refByName[name].First() : -1;
        var symByName = symbols.SelectMany(p => p.Value.Select(n => (n, p.Key))).ToLookup(p => p.n, p => p.Key);
        var addressIndex = image.Select((n, i) => (n.Address, Index: i + rows.Length)).ToDictionary(p => p.Address, p => p.Index);
        var nodes = new Node?[rows.Length + image.Length];
        static string Label(FingerprintBody b, IEnumerable<int> offsets) =>
            $"{b.Length}/{b.Sha256}/{string.Join(',', offsets)}/" +
            string.Join(',', b.Data.Select(d => $"{d.Offset}:{d.Kind}:{d.Displacement}:{d.Sha256}"));
        for (int i = 0; i < rows.Length; i++)
        {
            var r = rows[i];
            if (r.Body.Comparable)
                nodes[i] = new(Label(r.Body, r.Edges.Select(e => e.Offset)),
                    r.Edges.Select(e => Ref(e.Name)).ToArray());
        }
        for (int i = 0; i < image.Length; i++)
        {
            var b = image[i];
            if (b.Body.Comparable && !managed.Contains(b.Address))
                nodes[i + rows.Length] = new(Label(b.Body, b.Edges.Select(e => e.Offset)),
                    b.Edges.Select(e => addressIndex.GetValueOrDefault(e.Target, -1)).ToArray());
        }

        // 同一类中必须两侧都有成员。按每条边的目标类反复细分；失去下层候选的类随之删除，环无需专门截断。
        var labels = new Dictionary<string, int>(StringComparer.Ordinal);
        int Class(string key)
        {
            if (!labels.TryGetValue(key, out int c)) labels.Add(key, c = labels.Count + 1);
            return c;
        }
        int[] colors = nodes.Select(n => n == null ? 0 : Class(n.Label)).ToArray();
        while (true)
        {
            var sides = new byte[labels.Count + 1];
            for (int i = 0; i < colors.Length; i++) sides[colors[i]] |= (byte)(i < rows.Length ? 1 : 2);
            labels.Clear();
            var next = new int[colors.Length];
            for (int i = 0; i < colors.Length; i++)
            {
                if (colors[i] == 0 || sides[colors[i]] != 3) continue;
                var edges = nodes[i]!.Children;
                if (edges.Any(e => e < 0 || colors[e] == 0 || sides[colors[e]] != 3)) continue;
                next[i] = Class(colors[i] + "/" + string.Join(',', edges.Select(e => colors[e])));
            }
            if (next.AsSpan().SequenceEqual(colors)) break;
            colors = next;
        }
        var singles = Enumerable.Range(0, rows.Length).Where(i => colors[i] != 0)
            .GroupBy(i => colors[i]).Where(g => g.Count() == 1).ToDictionary(g => g.Key, g => g.Single());
        var paired = new Dictionary<ulong, int>();
        foreach (var group in image.Where(b => colors[addressIndex[b.Address]] != 0).GroupBy(b => colors[addressIndex[b.Address]]))
        {
            if (group.Count() != 1 || !singles.TryGetValue(group.Key, out int i) || NameOf(rows[i].Names) == null ||
                rows[i].Names.Any(n => Ref(n) != i)) continue;
            paired.Add(group.Single().Address, i);
        }
        while (true)
        {
            bool Closed(ulong address)
            {
                var actual = image[addressIndex[address] - rows.Length].Edges;
                var expected = rows[paired[address]].Edges;
                for (int k = 0; k < expected.Length; k++)
                    if (!paired.TryGetValue(actual[k].Target, out int child) || Ref(expected[k].Name) != child) return false;
                return true;
            }
            var lost = paired.Keys.Where(a => !Closed(a)).ToArray();
            if (lost.Length == 0) break;
            foreach (ulong a in lost) paired.Remove(a);
        }

        var anchors = registered.Concat(symbols.Keys).Where(a => !managed.Contains(a)).Distinct().Order().ToArray();
        bool Fits(ulong address) => paired.TryGetValue(address, out int i) &&
            (!symbols.TryGetValue(address, out var names) || NameOf(names) != null &&
            names.All(n => Ref(n) == i && symByName[n].Count() == 1));
        var missing = anchors.Where(a => !Fits(a)).ToArray();
        int aliasConflicts = symbols.Count(p => NameOf(p.Value) == null);
        Admitted = anchors.Length > 0 && missing.Length == 0;
        Admission = $"锚点 {anchors.Length}，闭包内 {anchors.Length - missing.Length}，未通过 {missing.Length}，同体闭包 {paired.Count}" +
            $"，动态或文件符号同址异名 {aliasConflicts}" +
            (missing.Length == 0 ? "" : $"，首个 0x{missing[0]:x} {string.Join('/', symbols.GetValueOrDefault(missing[0]) ?? ["登记入口"])}") +
            (Admitted ? "，准入" : "，整表拒用");
        if (!Admitted) return;
        foreach (var (a, i) in paired) names.TryAdd(a, new([.. rows[i].Names], "同体"));

        // 只从样本内依据或同体出发，统一收集提议后检查两个方向及已有命名，传递本身不能成为起点。
        var proposals = new List<(ulong Address, int Row, ulong Parent, int Offset)>();
        foreach (var (parent, name) in Names)
        {
            int r = Ref(name.Symbols[0]);
            if (r < 0 || !addressIndex.TryGetValue(parent, out int index)) continue;
            var edges = image[index - rows.Length].Edges;
            for (int k = 0; k < Math.Min(edges.Length, rows[r].Edges.Length); k++)
            {
                var e = edges[k];
                var re = rows[r].Edges[k];
                int child = Ref(re.Name);
                if (e.Offset == re.Offset && child >= 0 &&
                    NameOf(rows[child].Names) != null && !managed.Contains(e.Target))
                    proposals.Add((e.Target, child, parent, e.Offset));
            }
        }
        var addresses = proposals.Select(p => (p.Address, p.Row))
            .Concat(Names.Select(p => (Address: p.Key, Row: Ref(p.Value.Symbols[0])))).Distinct().ToArray();
        var byAddress = addresses.ToLookup(p => p.Address);
        var byName = addresses.ToLookup(p => p.Row);
        foreach (var p in proposals)
            if (byAddress[p.Address].Count() == 1 && byName[p.Row].Count() == 1)
                names.TryAdd(p.Address, new([.. rows[p.Row].Names], "传递", 1, p.Parent, p.Offset));
    }
}
