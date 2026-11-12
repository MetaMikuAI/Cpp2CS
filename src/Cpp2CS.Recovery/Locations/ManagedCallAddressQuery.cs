using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Locations;

/// <summary>调用中类型逐项相同的取址实参，同时为隐式检查提供访问前沿。</summary>
public sealed class ManagedCallAddressQuery(StateQueries state, CallNamingQuery calls, ManagedLocationQuery locations)
    : Query<CallIdentity, ImmutableArray<LocationView>>
{
    private readonly BoundSourceQuery sources = new(state);
    public override Outcome<ImmutableArray<LocationView>> Compute(QueryContext c, CallIdentity key)
    {
        var named = c.Get(calls, key); if (!named.IsSuccess) return named.Propagate<ImmutableArray<LocationView>>();
        if (named.Value.Kind != CallKind.Managed || named.Value.Candidates?.Candidates is not [{ Entry.Method: { } method, Binding.Value: { } binding }])
            return Outcome<ImmutableArray<LocationView>>.Success([]);
        var block = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(call => call.Identity == key));
        int index = 0;
        while (block.Statements[index] is not Call call || call.Identity != key) index++;
        var point = new Point(block.Identity, index);
        var views = ImmutableArray.CreateBuilder<LocationView>();
        var arguments = binding.Parameters.Select((bound, i) => (bound, Type: method.Concrete(method.Method.Parameters[i].Type))).ToList();
        if (binding.This is { } self && method.Method.Owner.IsValueType) arguments.Insert(0, (self, new ByRefRef(method.DeclaringType)));
        foreach (var (bound, type) in arguments)
        {
            if (type is not ByRefRef byref) continue;
            var term = c.Get(sources, new(bound.Source, point)); if (!term.IsSuccess) continue;
            var address = c.Get(locations.Addresses, term.Value); if (!address.IsSuccess) continue;
            var exact = address.Value.Where(v => v.Type.Equals(byref.Element)).ToArray();
            if (exact is [var view])
            {
                views.Add(view);
                // 实参按次序求值，只有首个取址访问可作为检查或初始化的前沿。
                break;
            }
        }
        return Outcome<ImmutableArray<LocationView>>.Success(views.ToImmutable());
    }
}
