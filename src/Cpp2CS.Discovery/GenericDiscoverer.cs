using System.Collections.Immutable;
using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;
using Cpp2CS.Spec.Catalog;

namespace Cpp2CS.Discovery;

/// <summary>按模板的最后一个效果定位操作，再按已绑定的操作数查找其余步骤。采纳由内核证明。</summary>
public sealed class GenericDiscoverer : IDiscoverer
{
    public string Name => "generic";

    public IEnumerable<Claim> Propose(FactView facts) =>
        facts.Effects.Failure is null ? new TemplateSearch(facts).Propose() : [];
}

internal sealed record Plan(CatalogEntry Entry, int Main)
{
    internal static IEnumerable<Plan> StraightLine()
    {
        foreach (var entry in OperationCatalog.Entries)
        {
            int main = -1;
            bool linear = true;
            for (int i = 0; i < entry.Steps.Length; i++)
            {
                var step = entry.Steps[i];
                if (step.Kind == StepKind.Require) continue;
                if (step.Indirect || step.Kind is not (StepKind.ThrowIf or StepKind.Read or StepKind.Write
                    or StepKind.Call or StepKind.ClassInitialize or StepKind.NewObject or StepKind.Throw))
                {
                    linear = false;
                    break;
                }
                main = i;
            }
            if (linear && (main >= 0 || entry.Result is not null)) yield return new(entry, main);
        }
    }
}

/// <summary>一次候选绑定。语义上的相等、位置与类型最终由证明核对。</summary>
internal sealed record Binding
{
    public ImmutableDictionary<int, Term> Operands { get; init; } = ImmutableDictionary<int, Term>.Empty;
    public ImmutableDictionary<int, Term> Results { get; init; } = ImmutableDictionary<int, Term>.Empty;
    public EntityRef? Entity { get; init; }
    public EntityRef? Owner { get; init; }
    public TypeShape? Subject { get; init; }
    public ImmutableHashSet<EffectRef> Required { get; init; } = [];
    public ImmutableHashSet<EffectRef> Optional { get; init; } = [];
    public Binding? Operand(int i, Term term) =>
        Operands.TryGetValue(i, out var old) && old != term ? null : this with { Operands = Operands.SetItem(i, term) };
    public Binding? Result(int i, Term term) =>
        Results.TryGetValue(i, out var old) && old != term ? null : this with { Results = Results.SetItem(i, term) };
    public Binding? WithEntity(EntityRef entity) => Entity is { } prior && prior != entity ? null : this with { Entity = entity };
    public Binding WithRead(NativeEffect effect) => this with { Optional = Optional.Add(EffectRef.Of(effect.Occurrence)) };
}

internal sealed partial class TemplateSearch(FactView facts)
{
    private static readonly Plan[] plans = [.. Plan.StraightLine()];
    private static readonly ILookup<StepKind, Plan> byMain = plans.Where(p => p.Main >= 0)
        .ToLookup(p => p.Entry.Steps[p.Main].Kind);
    private readonly EffectIndex index = new(facts.Effects);
    private readonly Dictionary<Term, TypeShape> types = facts.Effects.Arguments.ToDictionary(a => a.Value, a => a.Type);
    private TermPool Terms => facts.Effects.Snapshot.Terms;

    public IEnumerable<Claim> Propose()
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var effect in index.Effects)
        {
            if (effect.Result is { } result && effect.Callee?.Return is { } type) types[result] = type;
            if (effect.Kind == NativeEffectKind.NewObject && effect.Class is { Kind: TermKind.Entity } owner)
                types[effect.Value!] = new(StackKind.Object, facts.Layout.PointerBits, false, owner.Entity);
            if (EffectIndex.Kind(effect) is not { } kind) continue;
            var point = After(effect);
            foreach (var plan in byMain[kind])
                foreach (var bound in BindEffect(plan.Entry, plan.Main, effect, new()))
                    foreach (var claim in Finish(plan, bound, point))
                        if (seen.Add(claim.Key)) yield return claim;
        }

        foreach (var check in facts.Effects.Checks)
        {
            var passed = facts.Effects.Snapshot.Terminator(check.Edge.Source).Exits[1 - check.Edge.Exit];
            if (passed.Kind != ExitKind.Target) continue;
            foreach (var plan in byMain[StepKind.ThrowIf])
                if (BindCheck(plan.Entry.Steps[plan.Main], check, new()) is { } bound)
                    foreach (var claim in Finish(plan, bound with { Required = [EffectRef.Of(check.Edge)] }, new(passed.Target, 0)))
                        if (seen.Add(claim.Key)) yield return claim;
        }

        // 纯结果以值的使用点为落点。具名属性也可能来自原生读取，检查可以已由路径条件免除。
        foreach (var plan in plans.Where(p => p.Main < 0 || p.Entry.Steps[p.Main].Kind == StepKind.ThrowIf))
        {
            if (plan.Entry.Result is not { } pattern || pattern.Op == ValueOp.Operand) continue;
            foreach (var (value, use) in index.Values)
            {
                if (Match(pattern, value, new()) is not { } bound) continue;
                var point = value.Kind == TermKind.Result && facts.Effects.Effect(value.Occurrence) is { } producer
                    ? After(producer) : use;
                foreach (var claim in Complete(plan.Entry, plan.Entry.Steps.Length - 1, -1, bound, point, value))
                    if (seen.Add(claim.Key)) yield return claim;
            }
        }
    }

    private static ProgramPoint After(NativeEffect effect) => new(effect.Occurrence.Block, effect.Occurrence.Index + 1);

    private IEnumerable<Claim> Finish(Plan plan, Binding bound, ProgramPoint point) =>
        Complete(plan.Entry, plan.Entry.Steps.Length - 1, plan.Main, bound, point, null);

    private IEnumerable<Claim> Complete(CatalogEntry entry, int at, int skip, Binding bound, ProgramPoint point, Term? definition)
    {
        if (at < 0)
        {
            foreach (var claim in Claims(entry, bound, point, definition)) yield return claim;
            yield break;
        }
        var step = entry.Steps[at];
        foreach (var next in Candidates())
            foreach (var claim in Complete(entry, at - 1, skip, next, point, definition))
                yield return claim;

        IEnumerable<Binding> Candidates()
        {
            if (at == skip || step.Kind == StepKind.Require) { yield return bound; yield break; }
            if (step.Kind == StepKind.ThrowIf)
            {
                yield return bound;
                foreach (var check in index.Checks(step, bound))
                {
                    if (!index.Before(check.Edge.Source, point.Block) || BindCheck(step, check, bound) is not { } match) continue;
                    yield return match with { Optional = match.Optional.Add(EffectRef.Of(check.Edge)) };
                }
                yield break;
            }
            if (step.Kind == StepKind.ClassInitialize) yield return bound; // 幂等的初始化可由路径条件免除。
            var copies = bound.Required;
            foreach (var effect in index.Candidates(step, at, bound))
            {
                if (!index.Before(effect, point) || bound.Required.Contains(EffectRef.Of(effect.Occurrence))) continue;
                foreach (var match in BindEffect(entry, at, effect, bound))
                {
                    yield return match;
                    if (step.Kind == StepKind.NewObject && bound.Results.ContainsKey(at)) copies = copies.Union(match.Required);
                }
            }
            // 同一个接收者的不同叶子可以各自来自一次分配。
            if (copies.Count > bound.Required.Count + 1) yield return bound with { Required = copies };
        }
    }

    private IEnumerable<Claim> Claims(CatalogEntry entry, Binding bound, ProgramPoint point, Term? known)
    {
        foreach (var (definition, match) in Definitions())
        {
            int count = entry.OperandsFromSignature ? match.Operands.Count : entry.Operands.Length;
            if (match.Operands.Count != count || Enumerable.Range(0, count).Any(i => !match.Operands.ContainsKey(i))) continue;
            var operands = Enumerable.Range(0, count).Select(i => match.Operands[i]).ToImmutableArray();
            if (entry.SameKind && operands.Length > 1 && operands[0].Width != operands[1].Width) continue;
            if (definition is not null && match.Subject is { } subject && entry.ResultKind is ResultKind.Subject or ResultKind.Object)
                types.TryAdd(definition, subject);
            foreach (var occupied in Subsets([.. match.Optional.Except(match.Required).Order()], 0, match.Required))
                yield return new(entry.Id, match.Entity, operands, point, occupied, definition);
        }

        IEnumerable<(Term?, Binding)> Definitions()
        {
            if (known is not null || entry.Result is null) { yield return (known, bound); yield break; }
            var pattern = entry.Result;
            if (BoundValue(pattern, bound) is { } value) { yield return (value, bound); yield break; }
            // 调用的返回槽按栈宽给出；void 调用没有结果。
            if (entry.OperandsFromSignature && !entry.Constructs && bound.Subject is null) { yield return (null, bound); yield break; }
            foreach (var candidate in index.Using(pattern, bound))
                if (Match(pattern, candidate, bound) is { } match) yield return (candidate, match);
        }
    }

    private Term? BoundValue(TemplateValue pattern, Binding bound) => pattern.Op switch
    {
        ValueOp.Step => bound.Results.GetValueOrDefault(pattern.A),
        ValueOp.Operand => bound.Operands.GetValueOrDefault(pattern.A),
        ValueOp.FromStorage when BoundValue(pattern.Arguments[0], bound) is { } stored && bound.Subject is { } type => OnStack(stored, type),
        _ => null,
    };

    private Term OnStack(Term value, TypeShape type) =>
        type.Kind != StackKind.Int32 || value.Width >= 32 ? value :
        type.Signed ? Terms.SignExtend(value, 32) : Terms.ZeroExtend(value, 32);

    private static IEnumerable<ImmutableHashSet<EffectRef>> Subsets(EffectRef[] optional, int at, ImmutableHashSet<EffectRef> occupied)
    {
        if (at == optional.Length) { yield return occupied; yield break; }
        foreach (var full in Subsets(optional, at + 1, occupied.Add(optional[at]))) yield return full;
        foreach (var rest in Subsets(optional, at + 1, occupied)) yield return rest;
    }
}
