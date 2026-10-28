using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Structure;

public sealed record StateMachineFamily(MethodRef Kickoff, DefinitionRef Machine, MethodDef? MoveNext,
    ManagedBody? KickoffBody, ManagedBody? MoveNextBody, string Status, string? Reason);

/// <summary>族身份来自入口的 builder 调用与传入状态机类型，缺少成员时保留族级原因。</summary>
public static class StateMachineFamilies
{
    public static IReadOnlyList<StateMachineFamily> Read(IReadOnlyDictionary<MethodDef, ManagedBody> bodies)
    {
        var families = new List<StateMachineFamily>();
        foreach (var body in bodies.Values)
        {
            if (AsyncLifting.StateMachineOf(body) is not DefinitionRef machine) continue;
            var members = machine.Definition.Methods.Where(m => m.Name == "MoveNext" && !m.IsStatic && m.Parameters.Count == 0).ToArray();
            var moveNext = members.Length == 1 ? members[0] : null;
            var implementation = moveNext is null ? null : bodies.GetValueOrDefault(moveNext);
            var reason = members.Length != 1 ? "state-machine.ambiguous-member" : implementation is null ? "state-machine.missing-member"
                : body.Blocks.Concat(implementation.Blocks).SelectMany(b => b.Statements).Any(s => s is ManagedHole) ? "state-machine.partial-member" : null;
            families.Add(new(body.Method, machine, moveNext, body, implementation, reason is null ? "ready" : "blocked", reason));
        }
        return families;
    }
}
