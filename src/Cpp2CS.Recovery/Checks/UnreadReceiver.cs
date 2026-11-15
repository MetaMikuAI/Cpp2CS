using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;

namespace Cpp2CS.Recovery.Checks;

public sealed record UnreadReceiver(Term Value, FlowEdge? Branch = null, CallIdentity? Check = null);

/// <summary>未读接收者只取支配调用且访问前沿恰为该调用的显式判空对象。</summary>
public sealed class UnreadReceiverQuery(CheckQueries checks, ManagedTypes types) : Query<CallIdentity, UnreadReceiver?>
{
    private readonly FlowQueries flow = new();
    public override Outcome<UnreadReceiver?> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<UnreadReceiver?> None() => Outcome<UnreadReceiver?>.Success(null);
        var targetBlock = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(call => call.Identity == key));
        var call = targetBlock.Statements.OfType<Call>().Single(call => call.Identity == key);
        var point = new Point(targetBlock.Identity, targetBlock.Statements.IndexOf(call));
        var named = c.Get(checks.Calls, key);
        if (!named.IsSuccess) return named.Propagate<UnreadReceiver?>();
        if (call is not { Target: ImageFunction, Unwind: null } || named.Value.Kind != Naming.CallKind.Managed
            || named.Value.Candidates?.Candidates is not [{ Entry.Method: { } method }]
            || method.Method is not { IsStatic: false, IsOverridable: false, Owner.IsValueType: false, Name: not ".ctor" }) return None();
        bool Assignable(Term value) => c.Get(checks.Locations.Names, value) is
            { IsSuccess: true, Value: { Kind: Naming.ValueKind.ManagedReference, StaticType: { } type } }
            && types.IsAssignable(type, method.DeclaringType);
        Outcome<bool> Frontier(FrontierStart start)
        {
            var result = c.Get(checks.AccessFrontier, start);
            return result.IsSuccess ? Outcome<bool>.Success(!result.Value.HasCycle && !result.Value.ReachesExit
                && result.Value.Stops.Count == 1 && result.Value.Stops.Contains(point)) : result.Propagate<bool>();
        }
        foreach (var block in c.Snapshot.Blocks)
        {
            if (c.Step() is { } step) return Outcome<UnreadReceiver?>.Failure(step);
            if (block.End is Branch branch && c.Get(flow.PointDominates,
                new(new(block.Identity, block.Statements.Length), point)) is { IsSuccess: true, Value: true })
                foreach (var target in new[] { branch.True, branch.False }.Distinct())
                {
                    var proof = c.Get(checks.Checks, new(block.Identity, target));
                    if (!proof.IsSuccess) return proof.Propagate<UnreadReceiver?>();
                    if (proof.Value is not { Exception: "System.NullReferenceException", Subject.Value: { } subject } check
                        || !Assignable(subject)) continue;
                    var front = Frontier(FrontierStart.FromEdge(check.PassEdge));
                    if (!front.IsSuccess) return front.Propagate<UnreadReceiver?>();
                    if (front.Value) return Outcome<UnreadReceiver?>.Success(new(subject, check.PassEdge));
                }
            for (int i = 0; i < block.Statements.Length; i++)
            {
                if (block.Statements[i] is not Call { Unwind: null } check || check.Identity == key) continue;
                var after = new Point(block.Identity, i + 1);
                if (after != point && c.Get(flow.PointDominates, new(after, point)) is not { IsSuccess: true, Value: true }) continue;
                var classified = c.Get(checks.Calls, check.Identity);
                if (!classified.IsSuccess) return classified.Propagate<UnreadReceiver?>();
                if (classified.Value.Operation?.Il.Name != "NullCheck"
                    || classified.Value.Inputs?.GetValueOrDefault("value")?.Source is not TermSource input || !Assignable(input.Term)) continue;
                var front = Frontier(new(after));
                if (!front.IsSuccess) return front.Propagate<UnreadReceiver?>();
                if (front.Value) return Outcome<UnreadReceiver?>.Success(new(input.Term, Check: check.Identity));
            }
        }
        return None();
    }
}
