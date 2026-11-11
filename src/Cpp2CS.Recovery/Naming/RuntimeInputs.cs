using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Runtime;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Naming;

public sealed record RuntimeInputName(Term Value, RuntimeValueKind Kind) : ValueName;
/// <summary>登记操作的已绑定实参提供指针种类，不提供具体托管类型；冲突的种类不采纳。</summary>
public sealed class RuntimeInputKindsQuery(StateQueries state, CallNamingQuery calls)
    : Query<int, ImmutableDictionary<Term, RuntimeValueKind>>
{
    public override Outcome<ImmutableDictionary<Term, RuntimeValueKind>> Compute(QueryContext c, int key)
    {
        var kinds = new Dictionary<Term, HashSet<RuntimeValueKind>>();
        foreach (var call in c.Snapshot.Blocks.SelectMany(b=>b.Statements).OfType<Call>())
        {
            var classified=c.Get(calls,call.Identity);
            if (!classified.IsSuccess) return classified.Propagate<ImmutableDictionary<Term, RuntimeValueKind>>();
            if (classified.Value.Operation is not { } operation) continue;
            foreach (var input in operation.Inputs)
            {
                if (input.Use == RuntimeInputUse.Location || input.Kind is not
                    (RuntimeValueKind.ManagedReference or RuntimeValueKind.Class or RuntimeValueKind.Method)) continue;
                if (classified.Value.Inputs?.GetValueOrDefault(input.Name)?.Source is not TermSource source) continue;
                var value=c.Get(state.Resolve,source.Term);
                if (!value.IsSuccess) return value.Propagate<ImmutableDictionary<Term, RuntimeValueKind>>();
                if (value.Value.Width!=c.Snapshot.AddressWidth || value.Value.ContainsUndefined) continue;
                if (!kinds.TryGetValue(value.Value,out var uses)) kinds.Add(value.Value,uses=[]);
                uses.Add(input.Kind);
            }
        }
        return Outcome<ImmutableDictionary<Term, RuntimeValueKind>>.Success(kinds.Where(p=>p.Value.Count==1)
            .ToImmutableDictionary(p=>p.Key,p=>p.Value.Single()));
    }
}
