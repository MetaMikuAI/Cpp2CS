using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Discovery;

/// <summary>按效果种类、操作数与结果建索引。只展开纯项和效果已给出的地址，不解释块参数。</summary>
internal sealed class EffectIndex
{
    private readonly Dictionary<BlockId, int> order;
    private readonly ILookup<StepKind?, NativeEffect> byKind;
    private readonly ILookup<(StepKind?, Term), NativeEffect> operands;
    private readonly ILookup<EntityRef, NativeEffect> initializers;
    private readonly ILookup<ExceptionKind, ConditionalThrow> checks;
    private readonly ILookup<(ExceptionKind, Term), ConditionalThrow> checksUsing;
    private readonly ILookup<Term, Term> parents;
    private readonly Term[] terms;
    public NativeEffect[] Effects { get; }
    public EntityRef[] FieldEntities { get; }
    public List<(Term Term, ProgramPoint Use)> Values { get; } = [];

    public EffectIndex(EffectGraph graph)
    {
        order = graph.Order.Select((b, i) => (Block: new BlockId(b), Index: i)).ToDictionary(p => p.Block, p => p.Index);
        Effects = [.. graph.Effects];
        byKind = Effects.ToLookup(Kind);
        operands = Effects.SelectMany(e => Inputs(e).SelectMany(t => TermsOf(t)).Distinct()
            .Select(t => (e, t))).ToLookup(p => (Kind(p.e), p.t), p => p.e);
        initializers = Effects.Where(e => e.Kind == NativeEffectKind.ClassInitialize && e.Class?.Kind == TermKind.Entity)
            .ToLookup(e => e.Class!.Entity);
        checks = graph.Checks.ToLookup(c => c.Exception);
        checksUsing = graph.Checks.SelectMany(c => TermsOf(c.Condition, graph).Select(t => (c, t)))
            .ToLookup(p => (p.c.Exception, p.t), p => p.c);

        var seen = new HashSet<(BlockId, Term)>();
        void Use(Term? root, ProgramPoint point)
        {
            if (root is null) return;
            foreach (var term in TermsOf(root))
                if (seen.Add((point.Block, term))) Values.Add((term, point));
        }
        foreach (var b in graph.Order)
        {
            var block = new BlockId(b);
            for (int i = 0; i < graph.Snapshot.OccurrenceCount(block); i++)
            {
                if (graph.Effect(new(block, i)) is not { } effect) continue;
                var at = new ProgramPoint(block, i);
                foreach (var arg in effect.Arguments) Use(arg, at);
                if (effect.Kind == NativeEffectKind.Write) Use(effect.Value, at);
                if (effect.Kind == NativeEffectKind.Read) Use(effect.Value, new(block, i + 1));
                Use(effect.Address, at);
            }
            var end = new ProgramPoint(block, graph.Snapshot.OccurrenceCount(block));
            Use(graph.Condition(block), end);
            if (graph.Returned(block) is { } stored)
            {
                Use(stored, end);
                if (graph.Host.Return is { Kind: StackKind.Int32 } result && stored.Width < result.StackBits)
                    Use(result.Signed ? graph.Snapshot.Terms.SignExtend(stored, result.StackBits)
                        : graph.Snapshot.Terms.ZeroExtend(stored, result.StackBits), end);
            }
            Use(graph.ReturnSlot(block), end);
            // 出边行也是值的使用点。只读本行的表达式，不据此给目标块的参数配来源。
            var exits = graph.Snapshot.Terminator(block).Exits;
            for (int e = 0; e < exits.Length; e++)
            {
                var edge = new EdgeId(block, e);
                if (exits[e].Kind != ExitKind.Target || !graph.Live(edge)) continue;
                for (int i = 0; i < exits[e].Arguments.Length; i++)
                    Use(graph.EdgeArgument(edge, i), end);
            }
        }
        terms = [.. Values.Select(p => p.Term).Distinct()];
        FieldEntities = [.. terms.Where(t => t.Kind == TermKind.Entity && t.Entity.Kind == EntityKind.Field).Select(t => t.Entity)];
        parents = terms.SelectMany(t => t.Operands.Select(arg => (arg, t))).ToLookup(p => p.arg, p => p.t);
    }

    public static StepKind? Kind(NativeEffect effect) => effect.Kind switch
    {
        NativeEffectKind.Read => StepKind.Read,
        NativeEffectKind.Write => StepKind.Write,
        NativeEffectKind.Call => StepKind.Call,
        NativeEffectKind.Throw => StepKind.Throw,
        NativeEffectKind.NewObject => StepKind.NewObject,
        NativeEffectKind.ClassInitialize => StepKind.ClassInitialize,
        _ => null,
    };

    public bool Before(BlockId block, BlockId landing) => order[block] < order[landing];
    public bool Before(NativeEffect effect, ProgramPoint point) => effect.Occurrence.Block == point.Block
        ? effect.Occurrence.Index < point.Index : Before(effect.Occurrence.Block, point.Block);

    private static IEnumerable<Term> Inputs(NativeEffect effect)
    {
        foreach (var arg in effect.Arguments) yield return arg;
        if (effect.Address is { } address) yield return address;
        if (effect.Value is { } value) yield return value;
        if (effect.Class is { } cls) yield return cls;
    }

    public IEnumerable<NativeEffect> Candidates(TemplateStep step, int number, Binding bound)
    {
        var kind = step.Kind;
        if (kind == StepKind.NewObject && bound.Results.TryGetValue(number, out var receiver))
            return TermsOf(receiver).SelectMany(t => operands[(kind, t)]).Distinct();
        if (kind == StepKind.ClassInitialize && bound.Owner is { } owner) return initializers[owner];
        var keys = step.Values.SelectMany(Parameters).Where(bound.Operands.ContainsKey).Distinct().ToArray();
        return keys.Length == 0 ? byKind[kind] : keys.SelectMany(i => operands[(kind, bound.Operands[i])]).Distinct();
    }

    public IEnumerable<ConditionalThrow> Checks(TemplateStep step, Binding bound)
    {
        var operands = Parameters(step.Values[0]).Where(bound.Operands.ContainsKey).Distinct().ToArray();
        return operands.Length == 0 ? checks[step.Exception] : operands.SelectMany(i => checksUsing[(step.Exception, bound.Operands[i])]).Distinct();
    }

    public IEnumerable<Term> Using(TemplateValue value, Binding bound)
    {
        foreach (int i in Parameters(value))
            if (bound.Operands.TryGetValue(i, out var operand)) return Users(operand);
        return terms;
    }

    private IEnumerable<Term> Users(Term operand)
    {
        var pending = new Stack<Term>();
        var seen = new HashSet<Term>();
        pending.Push(operand);
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            yield return term;
            foreach (var parent in parents[term]) pending.Push(parent);
        }
    }

    private static IEnumerable<int> Parameters(TemplateValue value)
    {
        if (value.Op == ValueOp.Operand) yield return value.A;
        foreach (var argument in value.Arguments)
            foreach (int number in Parameters(argument)) yield return number;
    }

    internal static IEnumerable<Term> TermsOf(Term root, EffectGraph? reads = null)
    {
        var seen = new HashSet<Term>();
        var pending = new Stack<Term>();
        pending.Push(root);
        while (pending.TryPop(out var term))
        {
            if (!seen.Add(term)) continue;
            yield return term;
            foreach (var operand in term.Operands) pending.Push(operand);
            if (reads is not null && term.Kind == TermKind.Result && reads.Effect(term.Occurrence) is { Kind: NativeEffectKind.Read } read)
                pending.Push(read.Address!);
        }
    }
}
