using System.Collections.Immutable;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>
/// 对抗声明（设计第 15 节）。在恢复结果已被真实 IL 证明等价的用例上，把参照解释里的每条声明逐项变异后提交给证明入口：
/// 检查改配给别的检查、扩大占用、缩小占用、换落点、换操作数、换定义、换操作。
/// 裁判是真实 IL：被反驳的不再追究；拿到凭据的，连同该用例其余带凭据的声明（发现器提出的，以及别的拿到凭据的变异）
/// 重新选择并强制采纳它，能写全时写出的方法体必须与真实 IL 等价——不等价就是引擎放过了一条错误的声明。
/// 变异只依赖参照解释与效果图，不含针对某个用例的形态。
/// </summary>
internal sealed class Adversary
{
    private readonly SortedDictionary<string, (int Submitted, int Refuted, int Harmless, int Partial, int Wrong)> byKind = new(StringComparer.Ordinal);
    private readonly SortedDictionary<string, int> byReason = new(StringComparer.Ordinal);
    private readonly List<string> accepted = [];
    private readonly List<string> failures = [];
    private int cases;

    public int Failures => failures.Count;

    public void Run(string name, FactView view, RecoveryContext context, Explanation reference, IReadOnlyList<ProofOutcome> pool, Func<ManagedBody, bool> equivalent)
    {
        cases++;
        var graph = view.Effects;
        var snapshot = graph.Snapshot;
        var effects = new List<EffectRef>();
        foreach (var effect in graph.Effects)
            if (effect.Kind != NativeEffectKind.None) effects.Add(EffectRef.Of(effect.Occurrence));
        foreach (var check in graph.Checks) effects.Add(EffectRef.Of(check.Edge));
        var values = new List<Term>();
        foreach (var (value, _, _) in graph.Arguments) values.Add(value);
        foreach (var certificate in reference.Selected)
        {
            values.AddRange(certificate.Claim.Operands);
            if (certificate.Claim.Definition is { } defined) values.Add(defined);
        }
        var known = new HashSet<string>(reference.Selected.Select(c => c.Claim.Key), StringComparer.Ordinal);
        var granted = new List<(string Kind, string Text, ProofOutcome Outcome)>();

        foreach (var certificate in reference.Selected)
        {
            var claim = certificate.Claim;
            var mutants = new List<(string Kind, Claim Claim)>();
            void Add(string kind, string operation, ImmutableArray<Term> operands, ProgramPoint landing, IEnumerable<EffectRef> occupied, Term? definition) =>
                mutants.Add((kind, new Claim(operation, claim.Entity, operands, landing, occupied, definition)));

            // 检查改配：占用的一条检查边换成方法里的另一条检查边。
            foreach (var mine in claim.Occupied.Where(e => e.IsEdge))
                foreach (var other in graph.Checks.Select(c => EffectRef.Of(c.Edge)))
                    if (!claim.Occupied.Contains(other))
                        Add("检查改配", claim.Operation, claim.Operands, claim.Landing, claim.Occupied.Where(e => e != mine).Append(other), claim.Definition);
            // 扩大占用：多占一个别的效果。
            foreach (var extra in effects)
                if (!claim.Occupied.Contains(extra))
                    Add("扩大占用", claim.Operation, claim.Operands, claim.Landing, claim.Occupied.Append(extra), claim.Definition);
            // 缩小占用：少占一个效果。
            foreach (var dropped in claim.Occupied)
                Add("缩小占用", claim.Operation, claim.Operands, claim.Landing, claim.Occupied.Where(e => e != dropped), claim.Definition);
            // 换落点：每个块的开头，每个块的末尾，以及原落点的前一个位置。
            for (int b = 0; b < snapshot.BlockCount; b++)
                foreach (int index in (int[])[0, snapshot.OccurrenceCount(new BlockId(b))])
                    if (new ProgramPoint(new BlockId(b), index) != claim.Landing)
                        Add("换落点", claim.Operation, claim.Operands, new ProgramPoint(new BlockId(b), index), claim.Occupied, claim.Definition);
            if (claim.Landing.Index > 0)
                Add("换落点", claim.Operation, claim.Operands, new ProgramPoint(claim.Landing.Block, claim.Landing.Index - 1), claim.Occupied, claim.Definition);
            // 换操作数：两个操作数对调；一个操作数换成同宽的另一个值。
            for (int i = 0; i < claim.Operands.Length; i++)
            {
                for (int j = i + 1; j < claim.Operands.Length; j++)
                    if (claim.Operands[i].Width == claim.Operands[j].Width && !ReferenceEquals(claim.Operands[i], claim.Operands[j]))
                        Add("换操作数", claim.Operation, claim.Operands.SetItem(i, claim.Operands[j]).SetItem(j, claim.Operands[i]), claim.Landing, claim.Occupied, claim.Definition);
                foreach (var value in values)
                    if (value.Width == claim.Operands[i].Width && !ReferenceEquals(value, claim.Operands[i]))
                        Add("换操作数", claim.Operation, claim.Operands.SetItem(i, value), claim.Landing, claim.Occupied, claim.Definition);
            }
            // 换定义：定义换成同宽的另一个值。
            if (claim.Definition is { } definition)
                foreach (var value in values)
                    if (value.Width == definition.Width && !ReferenceEquals(value, definition))
                        Add("换定义", claim.Operation, claim.Operands, claim.Landing, claim.Occupied, value);
            // 换操作：目录里的每个别的操作。
            foreach (var entry in OperationCatalog.Entries)
                if (entry.Id != claim.Operation)
                    Add("换操作", entry.Id, claim.Operands, claim.Landing, claim.Occupied, claim.Definition);

            foreach (var (kind, mutant) in mutants)
            {
                if (!known.Add(mutant.Key)) continue;
                var outcome = Proof.Prove(context, mutant);
                var tally = byKind.GetValueOrDefault(kind);
                tally.Submitted++;
                if (outcome.Certificate is null)
                {
                    tally.Refuted++;
                    var refutation = outcome.Refutation!;
                    string reason = refutation.Layer == RefutationLayer.Explanation && refutation.Obligation is { } obligation
                        ? Refutation.Name(obligation) : refutation.Layer.ToString();
                    byReason[reason] = byReason.GetValueOrDefault(reason) + 1;
                }
                else
                    granted.Add((kind, $"{name}：{kind} {mutant.Operation} 占用 [{string.Join(", ", mutant.Occupied)}] 落点 B{mutant.Landing.Block.Index}.{mutant.Landing.Index}"
                        + $"（原：占用 [{string.Join(", ", claim.Occupied)}] 落点 B{claim.Landing.Block.Index}.{claim.Landing.Index}）", outcome));
                byKind[kind] = tally;
            }
        }

        // 真实 IL 裁判：逐条强制采纳，其余取这个用例全部带凭据的声明。
        ProofOutcome[] everything = [.. pool, .. granted.Select(g => g.Outcome)];
        foreach (var (kind, text, outcome) in granted)
        {
            var forced = Selection.Select(view, everything, outcome.Certificate);
            var body = forced is null ? null : Lowering.Lower(forced);
            var tally = byKind[kind];
            if (body is null || !body.Complete)
            {
                tally.Partial++;
                accepted.Add($"写不全 {text}");
            }
            else if (equivalent(body))
            {
                tally.Harmless++;
                accepted.Add($"等价   {text}");
            }
            else
            {
                tally.Wrong++;
                failures.Add(text);
            }
            byKind[kind] = tally;
        }
    }

    public void Report()
    {
        int submitted = byKind.Values.Sum(v => v.Submitted), refuted = byKind.Values.Sum(v => v.Refuted);
        int harmless = byKind.Values.Sum(v => v.Harmless), partial = byKind.Values.Sum(v => v.Partial);
        Console.WriteLine($"对抗声明：用例 {cases} 个，提交 {submitted} 条，被反驳 {refuted} 条；拿到凭据 {submitted - refuted} 条，"
            + $"其中并入解释后与真实 IL 等价 {harmless} 条、并入后写不全 {partial} 条、并入后与真实 IL 不等价 {failures.Count} 条");
        foreach (var (kind, v) in byKind)
            Console.WriteLine($"  {kind}：提交 {v.Submitted}，被反驳 {v.Refuted}，凭据而等价 {v.Harmless}，凭据而写不全 {v.Partial}，凭据而不等价 {v.Wrong}");
        Console.WriteLine($"  反驳的依据：{string.Join("，", byReason.Select(r => $"{r.Key} {r.Value}"))}");
        foreach (string line in failures) Console.WriteLine($"  放过了错误的声明：{line}");
        foreach (string line in accepted.Order(StringComparer.Ordinal)) Console.WriteLine($"  拿到凭据：{line}");
    }
}
