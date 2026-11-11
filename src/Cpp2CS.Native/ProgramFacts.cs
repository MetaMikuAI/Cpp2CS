using Cpp2CS.Native.Terms;

namespace Cpp2CS.Native;

internal static class ProgramFacts
{
    internal static IEnumerable<Term> Uses(Statement statement) => statement switch
    {
        MemoryRead read => [read.Address],
        MemoryWrite write => [write.Address, write.Value],
        TrapWhen trap => [trap.Condition],
        Call call => call.Arguments.Select(x => x.Value)
            .Concat(call.OutgoingArgumentArea is { } area ? [area] : []).Concat(call.Target is ComputedTarget target ? [target.Value] : []),
        DynamicAllocation allocation => [allocation.Size],
        _ => []
    };
    internal static IEnumerable<Term> Defines(Statement statement) => statement switch
    {
        MemoryRead read => [read.Result],
        Call call => call.Results.Select(x => x.Value),
        DynamicAllocation allocation => [allocation.Result],
        _ => []
    };
    internal static IEnumerable<Term> Uses(Terminator end) => end switch
    {
        Branch branch => [branch.Condition],
        JumpTable table => [table.Selector],
        Return result => result.Results.Select(x => x.Value),
        ResumeUnwind resume => [resume.Exception],
        _ => []
    };
    internal static IEnumerable<BlockIdentity> Targets(Terminator end) => end switch
    {
        Jump jump => [jump.Target],
        Branch branch => [branch.True, branch.False],
        JumpTable table => table.Cases.OrderBy(x => x.Value).Select(x => x.Target).Append(table.Default),
        _ => []
    };
}
