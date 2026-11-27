using System.Collections.Immutable;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Facts;

public sealed record AdmissionStrength(int Compared, int ComparedAnchors, int Anchors, int Incomparable);

public sealed record RuntimeName(ImmutableArray<string> Symbols, string Basis, int Depth = 0, ulong? Parent = null, int? Offset = null)
{
    public AdmissionStrength? Strength { get; init; }
    public ulong? ReferenceClass { get; init; }
    public string? ReferenceBuild { get; init; }
    public RuntimeOperation? Operation => RuntimeFingerprint.RegisteredOperation(Symbols);
    public string Name => Symbols.Length == 1 ? Symbols[0] : Operation?.Id ??
        (ReferenceClass is ulong id ? $"参照类 0x{id:x}（{Symbols.Length} 个符号）" : string.Join(" / ", Symbols));
}

/// <summary>代码引用的参照端是类代表，可写引用的参照端是原始地址。</summary>
public sealed record RuntimePair(ulong Address, ulong Reference, ReferenceKind Kind,
    string Basis, int Depth, ulong? Parent, int? Offset);

public sealed class RuntimeNaming
{
    private enum Comparison { Same, Different, Incomparable }
    private readonly record struct Pair(ulong Address, ulong Class);
    private sealed record Evidence(string Basis, int Depth = 0, ulong? Parent = null, int? Offset = null)
    {
        public RuntimePair Describe(Pair pair, ReferenceKind kind) =>
            new(pair.Address, pair.Class, kind, Basis, Depth, Parent, Offset);
    }
    private sealed record ClassInfo(FingerprintBody? Body, string? Key, ImmutableArray<string> Names);
    private readonly Dictionary<ulong, RuntimeName> names = [];
    private readonly SortedSet<string> examples = new(StringComparer.Ordinal);
    public IReadOnlyDictionary<ulong, RuntimeName> Names => names;
    public IReadOnlyCollection<string> Counterexamples => examples;
    public ImmutableArray<RuntimePair> AdmittedPairs { get; } = [];
    public AdmissionStrength? Strength { get; }
    public bool Admitted { get; }
    public string Admission { get; }

    public RuntimeNaming(RuntimeFingerprint reference, IReadOnlyDictionary<ulong, FingerprintBody> image,
        IReadOnlyDictionary<ulong, string[]> symbols, IReadOnlySet<ulong> managed, string? target)
    {
        foreach (var (address, aliases) in symbols)
            if (!managed.Contains(address) && aliases.Length != 0) names[address] = new([.. aliases], "符号");
        if (reference.Target != target) { Admission = $"目标不符 {reference.Target} / {target ?? "未知"}，整表拒用"; return; }

        // 表外函数只提供歧义反证，不进入锚点索引与传递目标。
        var outsideKeys = reference.Rows.Where(r => !r.Runtime && r.Body.Comparable)
            .Select(r => r.Body.LocalKey).ToHashSet(StringComparer.Ordinal);
        var runtime = reference.Rows.Where(r => r.Runtime).ToArray();
        var classes = runtime.GroupBy(r => r.Class).ToDictionary(g => g.Key, g =>
        {
            var body = g.First().Body;
            return new ClassInfo(body, body.Comparable ? body.LocalKey : null,
                [.. g.SelectMany(r => r.Names).Distinct().Order(StringComparer.Ordinal)]);
        });
        var classOf = runtime.ToDictionary(r => r.Address, r => r.Class);
        foreach (var group in reference.Imports.GroupBy(i => i.Name))
        {
            ulong id = group.Min(i => i.Address);
            foreach (var import in group) classOf.Add(import.Address, id);
            classes.Add(id, new(null, null, [group.Key]));
        }
        var byName = classes.SelectMany(c => c.Value.Names.Select(name => (name, c.Key))).ToLookup(p => p.name, p => p.Key);
        var byKey = classes.Where(c => c.Value.Key != null && !outsideKeys.Contains(c.Value.Key)).ToLookup(c => c.Value.Key!, c => c.Key);
        var local = image.Where(p => p.Value.Comparable).ToDictionary(p => p.Key, p => p.Value.LocalKey);
        Comparison Compare(Pair p)
        {
            if (classes[p.Class].Key is not string expected || !local.TryGetValue(p.Address, out var actual))
                return Comparison.Incomparable;
            return actual == expected ? Comparison.Same : Comparison.Different;
        }

        var proofs = new Dictionary<Pair, Evidence>();
        var dataProofs = new Dictionary<Pair, Evidence>();
        var queue = new Queue<Pair>();
        var assigned = new Dictionary<ulong, HashSet<ulong>>();
        var writable = new Dictionary<ulong, HashSet<ulong>>();
        var inverse = new Dictionary<ulong, HashSet<ulong>>();
        static HashSet<ulong> Add(Dictionary<ulong, HashSet<ulong>> map, ulong key, ulong value)
        {
            if (!map.TryGetValue(key, out var values)) map.Add(key, values = []);
            values.Add(value);
            return values;
        }

        void PairCode(Pair p, Evidence evidence)
        {
            if (managed.Contains(p.Address))
            {
                examples.Add($"托管入口 0x{p.Address:x} 被对到类 0x{p.Class:x}（{evidence.Basis}）");
                return;
            }
            if (!proofs.TryAdd(p, evidence)) return;
            Add(assigned, p.Address, p.Class);
            queue.Enqueue(p);
        }
        foreach (var (a, aliases) in symbols)
            foreach (ulong id in aliases.SelectMany(n => byName[n]).Distinct()) PairCode(new(a, id), new("锚点"));

        int compared = 0, comparedAnchors = 0, unknown = 0;
        void Propagate()
        {
            while (queue.TryDequeue(out var p))
            {
                var info = classes[p.Class];
                var evidence = proofs[p];
                var comparison = Compare(p);
                if (comparison == Comparison.Incomparable) { unknown++; continue; }
                compared++;
                if (evidence.Basis == "锚点") comparedAnchors++;
                var actual = image[p.Address];
                if (comparison == Comparison.Different)
                {
                    var expected = info.Body!;
                    string difference = actual.Length != expected.Length ? $"长度 {actual.Length}/{expected.Length}" :
                        actual.Sha256 != expected.Sha256 ? $"屏蔽后指令摘要 {actual.Sha256}/{expected.Sha256}" : "引用种类、位置或只读内容不同";
                    examples.Add($"局部不同 0x{p.Address:x} 类 0x{p.Class:x} {info.Names.FirstOrDefault()}（{difference}，{evidence.Basis}）");
                    continue;
                }
                for (int i = 0; i < actual.References.Length; i++)
                {
                    var r = info.Body!.References[i];
                    ulong a = actual.References[i].Target;
                    if (r.Kind == ReferenceKind.Code && classOf.TryGetValue(r.Target, out ulong child))
                        PairCode(new(a, child), new("传递", evidence.Depth + 1, p.Address, r.Offset));
                    else if (r.Kind == ReferenceKind.Writable)
                    {
                        dataProofs.TryAdd(new(a, r.Target), new("传递", evidence.Depth + 1, p.Address, r.Offset));
                        Add(writable, a, r.Target);
                        Add(inverse, r.Target, a);
                    }
                }
            }
        }

        // 一个候选指定了其每条引用应落到的类。未配对的代码引用可以一并证明；
        // 临时映射以地址为键，回到同一地址时必须仍是同一类。
        bool Closed(Pair root, IReadOnlyDictionary<ulong, ulong>? unique)
        {
            var pending = new Stack<Pair>();
            var group = new Dictionary<ulong, ulong>();
            pending.Push(root);
            while (pending.TryPop(out var p))
            {
                if (group.TryGetValue(p.Address, out ulong required))
                {
                    if (required != p.Class) return false;
                    continue;
                }
                if (p != root && assigned.TryGetValue(p.Address, out var known))
                {
                    if (!known.Contains(p.Class)) return false;
                    continue;
                }
                if (managed.Contains(p.Address) || Compare(p) != Comparison.Same || unique != null &&
                    (!unique.TryGetValue(p.Address, out var id) || id != p.Class)) return false;
                group.Add(p.Address, p.Class);
                var actual = image[p.Address].References;
                var expected = classes[p.Class].Body!.References;
                for (int i = 0; i < expected.Length; i++)
                {
                    var r = expected[i];
                    ulong a = actual[i].Target;
                    if (r.Kind == ReferenceKind.Code)
                    {
                        if (!classOf.TryGetValue(r.Target, out ulong child)) return false;
                        pending.Push(new(a, child));
                    }
                    if (r.Kind == ReferenceKind.Writable &&
                        (!writable.TryGetValue(a, out var values) || !values.Contains(r.Target))) return false;
                }
            }
            return true;
        }

        while (true)
        {
            Propagate();
            var unique = new Dictionary<ulong, ulong>();
            foreach (var (address, key) in local)
            {
                var matches = byKey[key].Where(id => Closed(new(address, id), null)).Take(2).ToArray();
                if (matches.Length == 1) unique.Add(address, matches[0]);
            }
            var group = unique.Select(kv => new Pair(kv.Key, kv.Value))
                .Where(p => !proofs.ContainsKey(p) && Closed(p, unique)).ToArray();
            if (group.Length == 0) break;
            foreach (var p in group) PairCode(p, new("同体"));
        }
        void Conflicts(Dictionary<ulong, HashSet<ulong>> map, string what)
        {
            foreach (var (a, values) in map.Where(p => p.Value.Count > 1))
                examples.Add($"{what} 0x{a:x} 对应 {string.Join('、', values.Order().Select(v => $"0x{v:x}"))}");
        }
        Conflicts(assigned, "一个函数地址多个类");
        Conflicts(writable, "一个可写地址多个参照地址");
        Conflicts(inverse, "一个参照可写地址多个样本地址");
        Admitted = examples.Count == 0;
        var strength = new AdmissionStrength(compared, comparedAnchors, proofs.Values.Count(e => e.Basis == "锚点"), unknown);
        Admission = $"配对 {proofs.Count}，已比较 {compared}（其中锚点 {comparedAnchors}），锚点总数 {strength.Anchors}" +
            $"，不可比 {unknown}，可写配对 {writable.Values.Sum(v => v.Count)}，反例 {examples.Count}，{(Admitted ? "准入" : "整表拒用")}";
        Strength = strength;
        if (!Admitted) return;
        AdmittedPairs = [.. proofs.Select(p => p.Value.Describe(p.Key, ReferenceKind.Code)),
            .. dataProofs.Select(p => p.Value.Describe(p.Key, ReferenceKind.Writable))];
        foreach (var (p, e) in proofs)
            if (!classes[p.Class].Names.IsEmpty)
                names[p.Address] = new(classes[p.Class].Names, e.Basis, e.Depth, e.Parent, e.Offset)
                    { Strength = strength, ReferenceClass = p.Class, ReferenceBuild = reference.BuildId };
    }
}
