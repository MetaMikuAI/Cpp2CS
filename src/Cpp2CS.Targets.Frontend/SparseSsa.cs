using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Draft = Cpp2CS.Targets.Frontend.FunctionLifter.Draft;

namespace Cpp2CS.Targets.Frontend;

/// <summary>从可观察的使用反向请求入口定义；未使用的寄存器不占用逐块状态。</summary>
internal sealed class SparseSsa(TermTable terms, Dictionary<ulong, Draft> blocks, Draft initial, RegisterConvention convention)
{
    private sealed class Phi(Draft block, Register register, Term result, MergeIdentity identity)
    {
        internal Draft Block { get; } = block;
        internal Register Register { get; } = register;
        internal Term Result { get; } = result;
        internal MergeIdentity Identity { get; } = identity;
        internal List<Incoming> Inputs { get; } = [];
    }
    private readonly Dictionary<(Draft, Register), Phi> requested = [];
    private readonly List<Phi> phis = [];
    private readonly Dictionary<Term, Term> aliases = [];
    private readonly HashSet<BlockIdentity> localMerges = [];
    private readonly Dictionary<Term, bool> globalValues = [];
    private Term Demand(Draft block, Register register)
    {
        if (block == initial)
        {
            if (initial.State.TryGetValue(register, out var value)) return value;
            if (convention.PreservedParts.Any(p => p.Register == register))
                return RegisterValues.KeepParts(terms, register, terms.Atom(new CallerValue(convention.CallerValues.IndexOf(register)), register.Width), convention.PreservedParts);
            return convention.CallerValues.Contains(register)
                ? terms.Atom(new CallerValue(convention.CallerValues.IndexOf(register)), register.Width)
                : terms.Undefined(register.Width);
        }
        if (block.Predecessors.Count == 0) return terms.Undefined(register.Width);
        if (requested.TryGetValue((block, register), out var existing)) return existing.Result;
        var id = new MergeIdentity();
        var phi = new Phi(block, register, terms.Atom(new ResultAtom(id), register.Width), id);
        requested.Add((block, register), phi);
        phis.Add(phi);
        return phi.Result;
    }
    internal ulong? BadStackAddress { get; private set; }
    internal IEnumerable<Block> Build()
    {
        var resolve = new TermRewrite(terms, t => t.Identity is RegisterInput input
            ? Demand(blocks[input.Address], input.Register) : null);
        var prepared = blocks.Values.OrderBy(b => b.Address).Select(b => new Block(b.Identity, [],
            b.Statements.Select(resolve.Statement).ToImmutableArray(), resolve.End(b.End), b.Handler) { Trace = new(b.TraceAddress) }).ToArray();
        var stackChecks = blocks.Values.SelectMany(b => b.StackChecks).Select(c => (c.Address, Value: resolve.Map(c.Value), c.Offset)).ToArray();
        for (int i = 0; i < phis.Count; i++)
        {
            var phi = phis[i];
            foreach (var predecessor in phi.Block.Predecessors.OrderBy(b => b == initial ? 0 : 1).ThenBy(b => b.Address))
            {
                var state = predecessor.UnwindStates.GetValueOrDefault(phi.Block.Identity) ?? predecessor.State;
                var value = state.TryGetValue(phi.Register, out var outgoing)
                    ? resolve.Map(outgoing) : Demand(predecessor, phi.Register);
                phi.Inputs.Add(new(predecessor.Identity, value));
            }
        }
        var control = new FunctionBuilder(terms, initial.Identity, convention.StackPointer.Width, new(initial.State[convention.StackPointer]));
        control.Blocks.Add(new(initial.Identity, [], [], initial.End));
        control.Blocks.AddRange(prepared);
        var dominance = new Dominance(control.Freeze());
        // 出口检查不从不可达分量推导跨块支配；局部定义经合流边传递，不能直接替代另一块的入口值。
        foreach (var block in prepared)
            if (!dominance.StrictlyDominates(initial.Identity, 0, block.Identity, 0)) localMerges.Add(block.Identity);
        int aliasCount;
        do
        {
            aliasCount = aliases.Count;
            Simplify();
            var substitute = new TermRewrite(terms, t => aliases.TryGetValue(t, out var value) ? Canonical(value) : null, followReplacement: true);
            foreach (var phi in phis.Where(p => !aliases.ContainsKey(p.Result)))
                for (int i = 0; i < phi.Inputs.Count; i++)
                    phi.Inputs[i] = phi.Inputs[i] with { Value = substitute.Map(phi.Inputs[i].Value) };
        } while (aliases.Count != aliasCount);
        var rewrite = new TermRewrite(terms, t => aliases.TryGetValue(t, out var value) ? Canonical(value) : null, followReplacement: true);
        Term Expected(long offset) => terms.Apply(new CoreOperator(CoreOperation.Add), convention.StackPointer.Width,
            initial.State[convention.StackPointer], terms.Constant(
                (new System.Numerics.BigInteger(offset) + (System.Numerics.BigInteger.One << convention.StackPointer.Width)) % (System.Numerics.BigInteger.One << convention.StackPointer.Width), convention.StackPointer.Width));
        foreach (var check in stackChecks)
            if (rewrite.Map(check.Value) != Expected(check.Offset)) { BadStackAddress = check.Address; break; }
        var retained = phis.Where(p => !aliases.ContainsKey(p.Result)).ToLookup(p => p.Block.Identity);
        var output = prepared.Select(block => block with
            {
                Merges = retained[block.Identity].OrderBy(p => p.Register.Name, StringComparer.Ordinal)
                    .Select(p => new Merge(p.Identity, p.Result, p.Inputs.Select(i => i with { Value = rewrite.Map(i.Value) }).ToImmutableArray())).ToImmutableArray(),
                Statements = block.Statements.Select(rewrite.Statement).ToImmutableArray(), End = rewrite.End(block.End)
            }).ToArray();
        // 替换后的规范化可能令使用消失；只保留仍能到达可观察使用的合流。
        var definitions = output.SelectMany(b => b.Merges).ToDictionary(m => m.Result);
        var needed = new HashSet<Term>();
        var todo = new Stack<Term>(output.SelectMany(b => b.Statements.SelectMany(FunctionLifter.Uses).Concat(FunctionLifter.Uses(b.End))));
        while (todo.TryPop(out var term))
        {
            if (!needed.Add(term)) continue;
            foreach (var child in term.Operands) todo.Push(child);
            if (definitions.TryGetValue(term, out var merge)) foreach (var input in merge.Inputs) todo.Push(input.Value);
        }
        foreach (var block in output)
            yield return block with { Merges = block.Merges.Where(m => needed.Contains(m.Result)).ToImmutableArray() };
    }
    private bool Global(Term value)
    {
        var todo = new Stack<(Term Value, bool Ready)>(); todo.Push((value, false));
        while (todo.TryPop(out var item))
        {
            if (globalValues.ContainsKey(item.Value)) continue;
            if (!item.Ready && !item.Value.Operands.IsEmpty)
            {
                todo.Push((item.Value, true));
                foreach (var child in item.Value.Operands) if (!globalValues.ContainsKey(child)) todo.Push((child, false));
                continue;
            }
            globalValues[item.Value] = (item.Value.Kind != TermKind.Atom || item.Value.Identity is EntryAtom or RootAtom or CallerValue)
                && item.Value.Operands.All(t => globalValues[t]);
        }
        return globalValues[value];
    }
    private Term Canonical(Term value)
    {
        var path = new List<Term>();
        while (aliases.TryGetValue(value, out var next)) { path.Add(value); value = next; }
        foreach (var term in path) aliases[term] = value;
        return value;
    }
    private void Simplify()
    {
        var users = new Dictionary<Term, List<Phi>>();
        foreach (var phi in phis)
            foreach (var input in phi.Inputs)
            {
                if (!users.TryGetValue(input.Value, out var list)) users.Add(input.Value, list = []);
                list.Add(phi);
            }
        var todo = new Queue<Phi>(phis);
        while (todo.TryDequeue(out var phi))
        {
            if (aliases.ContainsKey(phi.Result)) continue;
            var distinct = phi.Inputs.Select(i => Canonical(i.Value)).Where(t => t != phi.Result).Distinct().Take(2).ToArray();
            if (distinct.Length != 1) continue;
            var replacement = distinct[0];
            if (localMerges.Contains(phi.Block.Identity) && !Global(replacement)) continue;
            aliases.Add(phi.Result, replacement);
            if (!users.TryGetValue(phi.Result, out var dependent)) continue;
            if (!users.TryGetValue(replacement, out var destination)) users.Add(replacement, destination = []);
            foreach (var user in dependent) { todo.Enqueue(user); destination.Add(user); }
        }
        // 互相引用的合流可能共同只有一个外来值；按强连通分量消去。
        bool changed;
        do
        {
            changed = false;
            var live = phis.Where(p => !aliases.ContainsKey(p.Result)).ToDictionary(p => p.Result);
            var edges = live.ToDictionary(p => p.Key, p => p.Value.Inputs.Select(i => Canonical(i.Value)).Where(live.ContainsKey).Distinct().ToArray());
            var reversed = live.Keys.ToDictionary(t => t, _ => new List<Term>());
            foreach (var (from, targets) in edges) foreach (var target in targets) reversed[target].Add(from);
            var seen = new HashSet<Term>();
            var order = new List<Term>();
            foreach (var root in live.Keys)
            {
                var stack = new Stack<(Term Term, bool Exit)>();
                stack.Push((root, false));
                while (stack.TryPop(out var item))
                {
                    if (item.Exit) { order.Add(item.Term); continue; }
                    if (!seen.Add(item.Term)) continue;
                    stack.Push((item.Term, true));
                    foreach (var child in edges[item.Term]) stack.Push((child, false));
                }
            }
            seen.Clear();
            foreach (var root in order.AsEnumerable().Reverse())
            {
                if (!seen.Add(root)) continue;
                var component = new HashSet<Term> { root };
                var stack = new Stack<Term>(); stack.Push(root);
                while (stack.TryPop(out var term))
                    foreach (var parent in reversed[term]) if (seen.Add(parent)) { component.Add(parent); stack.Push(parent); }
                var external = component.SelectMany(t => live[t].Inputs).Select(i => Canonical(i.Value))
                    .Where(t => !component.Contains(t)).Distinct().Take(2).ToArray();
                if (external.Length != 1 || (localMerges.Count != 0 && component.Any(t => localMerges.Contains(live[t].Block.Identity)) && !Global(external[0]))) continue;
                foreach (var term in component) aliases[term] = external[0];
                changed = true;
            }
        } while (changed);
    }
}
