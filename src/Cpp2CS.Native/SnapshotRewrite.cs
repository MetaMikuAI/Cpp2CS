using System.Collections.Immutable;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Native;

/// <summary>只处理原生图与项替换，不依赖运行时语义；因此属于 Native，可供所有结构变换复用。</summary>
public sealed class SnapshotRewrite(NativeFunction source)
{
    public Dictionary<Term, Term> Replacements { get; } = [];
    public Dictionary<BlockIdentity, Block> Blocks { get; } = source.Blocks.ToDictionary(b => b.Identity);
    public HashSet<BlockIdentity> RemovedBlocks { get; } = [];
    public HashSet<Statement> RemovedStatements { get; } = [];

    public NativeFunction Apply()
    {
        var blocks = source.Blocks.Where(b => !RemovedBlocks.Contains(b.Identity)).Select(b => Blocks[b.Identity]).ToArray();
        var byId = blocks.ToDictionary(b => b.Identity);
        var reachable = new HashSet<BlockIdentity>(); var pending = new Stack<BlockIdentity>(); pending.Push(source.Entry);
        while (pending.TryPop(out var id))
        {
            if (!reachable.Add(id)) continue;
            var block = byId[id];
            foreach (var next in Targets(block.End).Concat(block.Statements.Where(s => !RemovedStatements.Contains(s))
                         .OfType<Call>().Where(c => c.Unwind is not null).Select(c => c.Unwind!))) pending.Push(next);
        }
        blocks = blocks.Where(b => reachable.Contains(b.Identity)).ToArray();
        var predecessors = blocks.ToDictionary(b => b.Identity, _ => new HashSet<BlockIdentity>());
        foreach (var b in blocks)
            foreach (var next in Targets(b.End).Concat(b.Statements.Where(s => !RemovedStatements.Contains(s)).OfType<Call>()
                         .Where(c => c.Unwind is not null).Select(c => c.Unwind!)).Distinct())
                predecessors[next].Add(b.Identity);
        blocks = blocks.Select(b => b with { Merges = b.Merges.Select(m => m with
            { Inputs = m.Inputs.Where(i => predecessors[b.Identity].Contains(i.Predecessor)).ToImmutableArray() }).ToImmutableArray() }).ToArray();
        foreach (var m in blocks.SelectMany(b => b.Merges))
            if (m.Inputs.Length == 1 && m.Inputs[0].Value != m.Result) Replacements.TryAdd(m.Result, m.Inputs[0].Value);
        var cache = new Dictionary<Term, Term>();
        var active = new HashSet<Term>();
        Term Map(Term value)
        {
            if (cache.TryGetValue(value, out var known)) return known;
            if (!active.Add(value)) throw new InvalidOperationException("项替换含循环。");
            var mapped = Replacements.TryGetValue(value, out var replacement) && replacement != value ? Map(replacement) : Rebuild(value, Map);
            active.Remove(value); cache[value] = mapped; return mapped;
        }
        var builder = new FunctionBuilder(source.Terms, source.Entry, source.AddressWidth, source.Frame)
        { ImageBase = source.ImageBase, ThreadPointer = source.ThreadPointer,
            IncomingArgumentArea = source.IncomingArgumentArea is { } area ? Map(area) : null };
        builder.Inputs.AddRange(source.Inputs);
        foreach (var b in blocks)
            builder.Blocks.Add(b with
            {
                Merges = b.Merges.Where(m => !Replacements.ContainsKey(m.Result)).Select(m => m with
                    { Inputs = m.Inputs.Select(i => i with { Value = Map(i.Value) }).ToImmutableArray() }).ToImmutableArray(),
                Statements = b.Statements.Where(s => !RemovedStatements.Contains(s)).Select(s => Rewrite(s, Map)).ToImmutableArray(),
                End = Rewrite(b.End, Map)
            });
        var result = builder.Freeze();
        var check = ExitChecker.Check(result);
        if (!check.IsValid) throw new InvalidOperationException($"快照改写违反原生契约（入口 0x{source.Blocks.First(b => b.Identity == source.Entry).Trace?.NativeAddress:x}）：" + string.Join("；", check.Violations));
        return result;
    }

    public static Term Rebuild(Term term, Func<Term, Term> map)
    {
        if (term.Operands.IsEmpty) return term;
        var values = term.Operands.Select(map).ToArray();
        return term.Kind switch
        {
            TermKind.Operation => term.Table.Apply(term.Operator!, term.Width, values),
            TermKind.Slice => term.Table.Slice(values[0], term.SliceLow!.Value, term.Width),
            TermKind.Concat => term.Table.Concat(values),
            _ => throw new InvalidOperationException("未登记的复合项。")
        };
    }
    public static Statement Rewrite(Statement statement, Func<Term, Term> map) => statement switch
    {
        MemoryRead r => r with { Address = map(r.Address) },
        MemoryWrite w => w with { Address = map(w.Address), Value = map(w.Value) },
        TrapWhen t => t with { Condition = map(t.Condition) },
        DynamicAllocation d => d with { Size = map(d.Size) },
        Call c => c with { Arguments = c.Arguments.Select(v => v with { Value = map(v.Value) }).ToImmutableArray(),
            Target = c.Target is ComputedTarget t ? new ComputedTarget(map(t.Value)) : c.Target,
            OutgoingArgumentArea = c.OutgoingArgumentArea is { } area ? map(area) : null },
        _ => throw new InvalidOperationException("未登记的语句。")
    };
    public static Terminator Rewrite(Terminator end, Func<Term, Term> map) => end switch
    {
        Branch b => b with { Condition = map(b.Condition) },
        JumpTable t => t with { Selector = map(t.Selector) },
        Return r => r with { Results = r.Results.Select(v => v with { Value = map(v.Value) }).ToImmutableArray() },
        ResumeUnwind u => u with { Exception = map(u.Exception) },
        Jump or Unreachable => end,
        _ => throw new InvalidOperationException("未登记的终结。")
    };
    public static IEnumerable<Term> Uses(Statement statement) => ProgramFacts.Uses(statement);
    public static IEnumerable<Term> Uses(Terminator end) => ProgramFacts.Uses(end);
    public static IEnumerable<BlockIdentity> Targets(Terminator end) => ProgramFacts.Targets(end);
    public static HashSet<Term> Dependencies(IEnumerable<Term> roots)
    {
        var found = new HashSet<Term>(); var pending = new Stack<Term>(roots);
        while (pending.TryPop(out var value))
            if (found.Add(value)) foreach (var operand in value.Operands) pending.Push(operand);
        return found;
    }
}
