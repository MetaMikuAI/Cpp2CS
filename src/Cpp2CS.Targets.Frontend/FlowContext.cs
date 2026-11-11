using System.Collections.Immutable;
using Cpp2CS.Native.Terms;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Draft = Cpp2CS.Targets.Frontend.FunctionLifter.Draft;

namespace Cpp2CS.Targets.Frontend;

/// <summary>仅提供唯一前驱链上的事实；不跨合流推断条件，也不展开循环。</summary>
internal sealed class FlowContext : IIndirectContext
{
    private readonly Dictionary<ulong, Draft> chain = [];
    public TermTable Terms { get; }
    public ImmutableArray<FlowCondition> Conditions { get; }
    public ulong? EntryAddress { get; }
    public IImage? Image { get; }
    public FunctionRange Range { get; }
    private readonly Dictionary<Term, MemoryRead> reads;
    private readonly Dictionary<ulong, Draft> drafts;
    public MemoryRead? ReadOf(Term result) => reads.GetValueOrDefault(result);
    internal FlowContext(TermTable terms, Draft current, ulong entry, FunctionRange range, IImage? image, IEnumerable<Draft> blocks)
    {
        Terms = terms;
        Range = range; Image = image; EntryAddress = entry;
        drafts = blocks.ToDictionary(b => b.Address);
        reads = drafts.Values.SelectMany(b => b.Statements).OfType<MemoryRead>().ToDictionary(r => r.Result);
        var conditions = ImmutableArray.CreateBuilder<FlowCondition>();
        var seen = new HashSet<Draft>();
        while (current.Address != entry && seen.Add(current) && current.Predecessors.Count == 1)
        {
            var previous = current.Predecessors[0];
            if (seen.Contains(previous)) break;
            chain[current.Address] = previous;
            if (previous.End is Cpp2CS.Native.Branch branch && branch.True != branch.False)
                conditions.Add(new(branch.Condition, branch.True == current.Identity));
            current = previous;
        }
        Conditions = conditions.ToImmutable();
    }
    public ImmutableArray<Term> InPredecessors(Term input)
    {
        if (input.Table != Terms) throw new ArgumentException("项必须来自本函数项表。");
        if (input.Identity is not RegisterInput register || !drafts.TryGetValue(register.Address, out var block)) return [];
        return [.. block.Predecessors.Select(p => p.State.TryGetValue(register.Register, out var value) ? value
            : Terms.Atom(new RegisterInput(p.Address, register.Register), register.Register.Width))];
    }
    public Term? InUniquePredecessor(Term input)
    {
        if (input.Table != Terms) throw new ArgumentException("项必须来自本函数项表。");
        if (input.Identity is not RegisterInput register || !chain.TryGetValue(register.Address, out var predecessor)) return null;
        return predecessor.State.TryGetValue(register.Register, out var value) ? value
            : Terms.Atom(new RegisterInput(predecessor.Address, register.Register), register.Register.Width);
    }
}
