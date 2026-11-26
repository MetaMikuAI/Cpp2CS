using System.Collections.Immutable;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;
using Cpp2CS.Spec.IL;

namespace Cpp2CS.Kernel;

/// <summary>洞在哪一层：事实（未命名、未定位）、目录、发现（没有声明触及）、解释（声明被反驳）、引擎与预算（证明没有做完）、选择（有凭据但没有被选中）、值（不可得的值）、骨架（控制转移写不出）。</summary>
public enum HoleLayer : byte { Fact, Catalog, Discovery, Explanation, Engine, Budget, Selection, Value, Skeleton }

/// <summary>
/// 洞（设计 9.8）：没被占用的效果，或不可得的值。Layer 与 Obligation 是归类：所在的层，以及触及它的声明里最接近成立的那条被反驳的义务。
/// Derived：由别的洞导致。
/// </summary>
public sealed record Hole(EffectRef? Effect, string What, HoleLayer Layer, Obligation? Obligation, string Reason, bool Derived);

/// <summary>
/// 解释（设计 9.7）：选中的一组带凭据的声明，占用两两不交、值可得、落点约束成立；加上洞的记录。只能由选择构造。
/// Inexact：某个分量的求解超出预算，保留了前一级的结果。
/// </summary>
public sealed class Explanation
{
    public ImmutableArray<Certificate> Selected { get; }
    public ImmutableArray<Hole> Holes { get; }
    public bool Inexact { get; }
    /// <summary>试写的次数。</summary>
    public int Evaluations { get; }
    internal EffectGraph Graph { get; }
    internal IEntityMetadata Metadata { get; }
    internal ImmutableArray<ProofOutcome> Outcomes { get; }

    /// <summary>独立洞的个数（派生的不计）。</summary>
    public int IndependentHoles => Holes.Count(h => !h.Derived);

    internal Explanation(EffectGraph graph, IEntityMetadata metadata, ImmutableArray<ProofOutcome> outcomes, ImmutableArray<Certificate> selected,
        ImmutableArray<Hole> holes, bool inexact, int evaluations)
    {
        Graph = graph;
        Metadata = metadata;
        Outcomes = outcomes;
        Selected = selected;
        Holes = holes;
        Inexact = inexact;
        Evaluations = evaluations;
    }
}

/// <summary>
/// 选择（设计 9.7）：唯一决定采纳哪些声明的步骤。约束由这里机械地核对；目标是洞最少，并列时取登记在前的规则、再按稳定键。
/// 规则按目录项的登记次序编号，逐级进行：第 k 级只在仍有洞、且被第 k 号规则的声明触及的分量里重新求解，洞严格减少才替换。
/// </summary>
public static class Selection
{
    public static Explanation Select(FactView facts, IReadOnlyList<ProofOutcome> outcomes, int budget = 2_000) =>
        Select(facts, outcomes, null, budget)!;

    /// <summary>
    /// 指定一条必须采纳的声明再选择：其余声明里与它占用重叠的不参加。没有一组满足约束的声明包含它时为空。
    /// 供验证使用（设计第 15 节的对抗声明）：一条拿到凭据的声明并入解释之后，写出的方法体仍须与真实 IL 等价。
    /// </summary>
    public static Explanation? Select(FactView facts, IReadOnlyList<ProofOutcome> outcomes, Certificate? pinned, int budget = 2_000)
    {
        var graph = facts.Effects;
        string digest = graph.Snapshot.DigestText;
        var certificates = new List<Certificate>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var outcome in outcomes)
            if (outcome.Certificate is { } certificate && certificate.SnapshotDigest == digest && seen.Add(certificate.Claim.Key)
                && (pinned is null || (certificate != pinned && !certificate.Claim.Occupied.Any(pinned.Claim.Occupied.Contains)))) certificates.Add(certificate);
        if (pinned is not null && pinned.SnapshotDigest != digest) return null;
        var rule = new Dictionary<Certificate, int>();
        foreach (var certificate in certificates) rule[certificate] = OperationCatalog.Entries.IndexOf(OperationCatalog.Get(certificate.Claim.Operation));
        certificates.Sort((a, b) => rule[a] != rule[b] ? rule[a].CompareTo(rule[b]) : string.CompareOrdinal(a.Claim.Key, b.Claim.Key));

        var all = outcomes.ToImmutableArray();
        int evaluations = 0;
        bool inexact = false;
        // 试写：不满足约束时为空；否则是这组声明写出之后的洞。
        IReadOnlyList<Hole>? Evaluate(IReadOnlyList<Certificate> selection)
        {
            if (pinned is not null) selection = [.. selection, pinned];
            if (!Consistent(graph, selection)) return null;
            evaluations++;
            var writer = new Writer(graph, facts.Metadata, selection, all);
            writer.Run();
            return writer.Unwritable.Count > 0 ? null : writer.Holes;
        }
        static int Count(IReadOnlyList<Hole>? holes) => holes?.Count(h => !h.Derived) ?? int.MaxValue;

        var current = new List<Certificate>();
        var holes = Evaluate(current);
        foreach (int level in rule.Values.Distinct().Order())
        {
            if (Count(holes) == 0) break;
            var candidates = certificates.Where(c => rule[c] <= level).ToList();
            foreach (var component in Components(candidates))
            {
                if (component.TrueForAll(c => rule[c] != level)) continue;
                var others = current.Where(c => !component.Contains(c)).ToList();
                // 分量里按效果逐个决定：由哪条声明占用，或者留作洞。
                var effects = component.SelectMany(c => c.Claim.Occupied).Distinct().Order().ToList();
                List<Certificate>? best = null;
                var bestHoles = holes;
                bool exhausted = false;
                var chosen = new List<Certificate>();
                var taken = new HashSet<EffectRef>();
                void Search(int at, int unoccupied)
                {
                    if (exhausted || unoccupied >= Count(bestHoles)) return;
                    while (at < effects.Count && taken.Contains(effects[at])) at++;
                    if (at == effects.Count)
                    {
                        if (evaluations >= budget) { exhausted = true; return; }
                        if (Evaluate([.. others, .. chosen]) is { } found && Count(found) < Count(bestHoles)) (best, bestHoles) = ([.. chosen], found);
                        return;
                    }
                    var effect = effects[at];
                    foreach (var candidate in component)
                    {
                        // 每组声明只枚举一次：一条声明在它占用的、尚未决定的第一个效果上被选入。
                        var occupied = candidate.Claim.Occupied;
                        if (!occupied.Contains(effect) || occupied.Any(taken.Contains) || occupied.Any(o => effects.IndexOf(o) < at)) continue;
                        chosen.Add(candidate);
                        foreach (var o in occupied) taken.Add(o);
                        Search(at + 1, unoccupied);
                        foreach (var o in occupied) taken.Remove(o);
                        chosen.RemoveAt(chosen.Count - 1);
                    }
                    Search(at + 1, unoccupied + 1);
                }
                Search(0, 0);
                if (exhausted) { inexact = true; continue; }
                if (best is not null) (current, holes) = ([.. others, .. best], bestHoles);
            }
        }
        if (holes is null) return null;
        if (pinned is not null) current.Add(pinned);
        current.Sort((a, b) => string.CompareOrdinal(a.Claim.Key, b.Claim.Key));
        return new Explanation(graph, facts.Metadata, all, [.. current], [.. holes], inexact, evaluations);
    }

    /// <summary>占用两两不交，落点约束成立（设计 9.4）。值可得由试写核对。</summary>
    private static bool Consistent(EffectGraph graph, IReadOnlyList<Certificate> selection)
    {
        var owner = new Dictionary<EffectRef, Certificate>();
        foreach (var certificate in selection)
            foreach (var effect in certificate.Claim.Occupied)
                if (!owner.TryAdd(effect, certificate)) return false;
        bool NotLater(ProgramPoint a, ProgramPoint b) =>
            a.Block == b.Block ? a.Index <= b.Index : graph.Shape.Dominates(a.Block, b.Block);
        foreach (var certificate in selection)
        {
            var landing = certificate.Claim.Landing;
            // 依赖的效果：确立者（凭据记的是它所在的块：块末的检查，或块里的事件）若被别的声明占用，那条声明的落点不晚于本声明的落点。
            // 按块核对比按效果核对保守。没被占用的留在原位，原位在本声明的落点之前。
            foreach (var block in certificate.Before)
                foreach (var (effect, other) in owner)
                    if (effect.Block == block && other != certificate && !NotLater(other.Claim.Landing, landing)) return false;
            // 推后的旁观效果：必须由落点不早于本声明的声明占用。留在原位的洞在本声明的落点之前，不满足。
            foreach (var effect in certificate.After)
                if (!owner.TryGetValue(effect, out var other) || other == certificate || !NotLater(landing, other.Claim.Landing)) return false;
        }
        foreach (var group in selection.GroupBy(c => c.Claim.Landing))
            if (Order([.. group]) is null) return false;
        return true;
    }

    /// <summary>落点相同时 first 必须排在 second 之前：second 依赖 first 占用的确立者，或 first 把 second 占用的旁观效果推后。</summary>
    private static bool Precedes(Certificate first, Certificate second) =>
        second.Before.Any(block => first.Claim.Occupied.Any(e => e.Block == block))
        || first.After.Any(second.Claim.Occupied.Contains);

    /// <summary>落点相同的声明的写出次序：先按落点约束，再按稳定键。约束成环时为空。</summary>
    internal static List<Certificate>? Order(List<Certificate> here)
    {
        var pending = here.OrderBy(c => c.Claim.Key, StringComparer.Ordinal).ToList();
        var ordered = new List<Certificate>(pending.Count);
        while (pending.Count > 0)
        {
            int next = pending.FindIndex(c => !pending.Exists(other => other != c && Precedes(other, c)));
            if (next < 0) return null;
            ordered.Add(pending[next]);
            pending.RemoveAt(next);
        }
        return ordered;
    }

    /// <summary>声明按占用重叠、落点约束、值的供求连成分量（设计 9.7）。</summary>
    private static List<List<Certificate>> Components(List<Certificate> candidates)
    {
        int[] parent = [.. Enumerable.Range(0, candidates.Count)];
        int Find(int x) => parent[x] == x ? x : parent[x] = Find(parent[x]);
        var subterms = candidates.Select(c => Subterms(c.Claim.Operands)).ToList();
        for (int i = 0; i < candidates.Count; i++)
            for (int j = i + 1; j < candidates.Count; j++)
            {
                var (a, b) = (candidates[i], candidates[j]);
                bool related = a.Claim.Occupied.Any(b.Claim.Occupied.Contains)
                    || Precedes(a, b) || Precedes(b, a)
                    || (a.Claim.Definition is { } x && subterms[j].Contains(x)) || (b.Claim.Definition is { } y && subterms[i].Contains(y));
                if (related) parent[Find(i)] = Find(j);
            }
        return [.. Enumerable.Range(0, candidates.Count).GroupBy(Find).Select(g => g.Select(i => candidates[i]).ToList())];
    }

    private static HashSet<Term> Subterms(ImmutableArray<Term> roots)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<Term>(roots);
        while (pending.Count > 0)
        {
            var current = pending.Pop();
            if (!seen.Add(current)) continue;
            foreach (var operand in current.Operands) pending.Push(operand);
        }
        return seen;
    }
}

/// <summary>
/// 托管方法体里的一条指令。Opcode 是助记符；Target 是转移的标号；Entity 是它引用的元数据实体。
/// 两种伪指令：“.label”标出一个标号（Operand 是标号）；“.unrecovered”是一个洞（Operand 是洞的序号）。
/// </summary>
public readonly record struct ManagedInstruction(string Opcode, long Operand = 0, EntityRef? Entity = null, int Target = -1);

/// <summary>
/// 托管方法体：下降的产物，只能由下降构造（设计第 10、11 节）。指令引用元数据实体与标号，局部变量带类型；
/// 洞在原位是伪指令“.unrecovered”，操作数是 Holes 里的序号。
/// </summary>
public sealed class ManagedBody
{
    public MethodShape Host { get; }
    public ImmutableArray<ManagedInstruction> Instructions { get; }
    public ImmutableArray<TypeShape> Locals { get; }
    public ImmutableArray<Hole> Holes { get; }
    public bool Complete => Holes.IsEmpty;

    internal ManagedBody(MethodShape host, ImmutableArray<ManagedInstruction> instructions, ImmutableArray<TypeShape> locals, ImmutableArray<Hole> holes)
    {
        Host = host;
        Instructions = instructions;
        Locals = locals;
        Holes = holes;
    }

    private sealed class Table(List<EntityRef> entities) : ITokenResolver
    {
        private EntityRef At(int token) => token >= 1 && token <= entities.Count ? entities[token - 1] : throw new ExpansionException($"记号 {token} 不在表里", "");
        public EntityRef Method(int token) => At(token);
        public EntityRef Field(int token) => At(token);
        public EntityRef Type(int token) => At(token);
        public EntityRef String(int token) => At(token);
    }

    /// <summary>
    /// 没有洞的方法体写成 IL 字节（ECMA-335 III.1.2），供按目录展开。引用实体的指令带一个记号，记号是 Tokens 表里的序号；
    /// 转移一律用长形式。有洞时为空。
    /// </summary>
    public (MethodBody Body, ITokenResolver Tokens)? Encode()
    {
        if (!Complete) return null;
        var il = new IlWriter();
        var entities = new List<EntityRef>();
        foreach (var instruction in Instructions)
        {
            if (instruction.Opcode == ".label") { il.Mark((int)instruction.Operand); continue; }
            var opcode = IlWriter.Find(instruction.Opcode) ?? throw new InvalidOperationException($"指令表里没有 {instruction.Opcode}");
            switch (opcode.Operand)
            {
                case OperandKind.None: il.Plain(opcode.Name); break;
                case OperandKind.Int32: il.Int32(opcode.Name, (int)instruction.Operand); break;
                case OperandKind.Variable16: il.Variable(opcode.Name, (int)instruction.Operand); break;
                case OperandKind.Branch32: il.Branch(opcode.Name, instruction.Target); break;
                case OperandKind.Method or OperandKind.Field or OperandKind.Type or OperandKind.String or OperandKind.Token:
                    entities.Add(instruction.Entity ?? throw new InvalidOperationException($"{instruction.Opcode} 没有带实体"));
                    il.Int32(opcode.Name, entities.Count);
                    break;
                default: throw new InvalidOperationException($"{instruction.Opcode} 的操作数形式 {opcode.Operand} 不在写出的范围里");
            }
        }
        return (new MethodBody(Host, Locals, il.Build(), 0, true), new Table(entities));
    }
}

/// <summary>下降（设计第 10 节）：只读解释与事实，照着写出。</summary>
public static class Lowering
{
    public static ManagedBody Lower(Explanation explanation)
    {
        var writer = new Writer(explanation.Graph, explanation.Metadata, explanation.Selected, explanation.Outcomes);
        writer.Run();
        if (writer.Unwritable.Count > 0) throw new InvalidOperationException("解释里有写不出的声明：选择没有核对值可得");
        return new ManagedBody(writer.Host, [.. writer.Code], writer.Locals, [.. writer.Holes]);
    }
}
