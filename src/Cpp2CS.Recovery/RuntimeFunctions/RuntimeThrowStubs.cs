using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.RuntimeFunctions;

/// <summary>消去不可观察效果后，替换桩只剩一次登记的 profile 抛出和帧内写入。</summary>
public static class RuntimeThrowStubs
{
    public static bool IsStub(NativeFunction function, CallNamingQuery calls)
    {
        if (function.Blocks.Any(b => b.Handler is not null)) return false;
        var events = function.Blocks.SelectMany(b => b.Statements).OfType<Call>().ToArray();
        if (events is not [var thrown] || !thrown.DoesNotReturn || thrown.Unwind is not null
            || calls.RuntimeIdentity(thrown.Target)?.Operation.Il.Name != "ThrowProfile") return false;
        var state = new StateQueries(); var c = state.CreateContext(function);
        foreach (var statement in function.Blocks.SelectMany(b => b.Statements))
        {
            if (statement is MemoryRead { Acquire: true } or MemoryWrite { Release: true }) return false;
            if (statement is Call or MemoryRead) continue;
            if (statement is not MemoryWrite write) return false;
            var address = c.Get(state.Resolve, write.Address);
            if (!address.IsSuccess || c.Get(state.Locations, new(address.Value, write.Width)) is not { IsSuccess: true, Value.Region: Region.Frame }) return false;
        }
        var block = function.Blocks.Single(b => b.Statements.Contains(thrown));
        var point = new Point(block.Identity, block.Statements.IndexOf(thrown));
        var frontier = new EventFrontierQuery((_, at) => Outcome<bool>.Success(at == point));
        return c.Get(frontier, new(new(function.Entry, 0))) is { IsSuccess: true, Value: { ReachesExit: false, HasCycle: false } result }
            && result.Stops.SetEquals([point]);
    }
}
