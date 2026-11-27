using Cpp2CS.Kernel;
using Cpp2CS.Kernel.Facts;
using Cpp2CS.Kernel.Forward;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Discovery;

/// <summary>直接基类的构造函数被内联时，按现场实参提出对直接基类的调用（设计 9.3、14.2）。</summary>
public sealed class BaseConstructorDiscoverer(Func<EntityRef, int, IEnumerable<MethodShape>> constructors) : IDiscoverer
{
    public string Name => "base-constructor";

    public IEnumerable<Claim> Propose(FactView facts)
    {
        var graph = facts.Effects;
        var host = graph.Host;
        if (graph.Failure != null || facts.Metadata.IsInstanceConstructor(host.Entity) != true
            || facts.Metadata.BaseOf(host.DeclaringType) is not { } parent
            || CallLegality.HostThis(graph.Snapshot, host) is not { } receiver) yield break;

        foreach (var call in graph.Effects)
        {
            if (call.Kind != NativeEffectKind.Call || call.Callee is not { } callee
                || graph.Snapshot.Occurrence(call.Occurrence) is not CallOccurrence { Target.IsConstant: true }
                || callee.DeclaringType == host.DeclaringType || callee.DeclaringType == parent
                || facts.Metadata.IsInstanceConstructor(callee.Entity) != true
                || call.Arguments.IsEmpty || call.Arguments[0] != receiver) continue;
            var site = call.Occurrence;
            foreach (var constructor in constructors(parent, call.Arguments.Length))
                if (constructor.Parameters.Select(p => p.StackBits).SequenceEqual(call.Arguments.Select(a => a.Width)))
                    yield return new("call.instance", constructor.Entity, call.Arguments,
                        new(site.Block, site.Index + 1), [EffectRef.Of(site)], null);
        }
    }
}
