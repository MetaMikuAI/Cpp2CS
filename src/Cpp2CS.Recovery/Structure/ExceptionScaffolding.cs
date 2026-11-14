using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

/// <summary>托管包装假设下，私有 C++ 捕获操作不产生托管展开；先移去这些边及其不可达清理。</summary>
public static class ExceptionScaffolding
{
    public static NativeFunction Project(NativeFunction function, CallNamingQuery calls, bool splitEntries = false)
    {
        var rewrite = new SnapshotRewrite(function); bool changed = false;
        foreach (var block in function.Blocks)
        {
            var statements = block.Statements.Select(statement =>
            {
                if (statement is not Call { Unwind: not null } call || calls.RuntimeIdentity(call.Target)?.Operation.Name is not
                    ("BeginCatch" or "EndCatch" or "CxxGetExceptionPointer" or "CxxAllocateException" or "CxxFreeException")) return statement;
                changed = true;
                return (Statement)(call with { Unwind = null });
            }).ToImmutableArray();
            rewrite.Blocks[block.Identity] = block with { Statements = statements };
        }
        var projected = changed ? rewrite.Apply() : function;
        return splitEntries ? SplitEntries(projected) : projected;
    }

    /// <summary>受保护调用前已有调用时，在前一次调用之后切块，使 try 可以从精确的程序点进入。</summary>
    private static NativeFunction SplitEntries(NativeFunction function)
    {
        var pieces = new Dictionary<BlockIdentity, Block[]>();
        foreach (var block in function.Blocks)
        {
            var cuts = new List<int> { 0 }; int previous = -1;
            for (int i = 0; i < block.Statements.Length; i++)
                if (block.Statements[i] is Call call)
                {
                    if (call.Unwind is not null && previous >= 0 && previous + 1 != cuts[^1]) cuts.Add(previous + 1);
                    previous = i;
                }
            if (cuts.Count == 1) continue;
            var ids = cuts.Select((_, i) => i == 0 ? block.Identity : new BlockIdentity(block.Identity)).ToArray();
            pieces.Add(block.Identity, cuts.Select((start, i) => new Block(ids[i], i == 0 ? block.Merges : [],
                block.Statements[start..(i + 1 == cuts.Count ? block.Statements.Length : cuts[i + 1])],
                i + 1 == cuts.Count ? block.End : new Jump(ids[i + 1]), i == 0 ? block.Handler : null)
                { Trace = i == 0 ? block.Trace : block.Statements[start].Trace ?? block.Trace }).ToArray());
        }
        if (pieces.Count == 0) return function;
        var builder = new FunctionBuilder(function.Terms, function.Entry, function.AddressWidth, function.Frame)
        { ImageBase = function.ImageBase, ThreadPointer = function.ThreadPointer, IncomingArgumentArea = function.IncomingArgumentArea };
        builder.Inputs.AddRange(function.Inputs);
        foreach (var block in function.Blocks.SelectMany(block => pieces.GetValueOrDefault(block.Identity) ?? [block]))
            builder.Blocks.Add(block with { Merges = block.Merges.Select(merge => merge with
            {
                Inputs = merge.Inputs.SelectMany(input => pieces.TryGetValue(input.Predecessor, out var predecessors)
                    ? predecessors.Where(predecessor => SnapshotRewrite.Targets(predecessor.End).Contains(block.Identity)
                        || predecessor.Statements.OfType<Call>().Any(call => call.Unwind == block.Identity))
                        .Select(predecessor => input with { Predecessor = predecessor.Identity })
                    : [input]).ToImmutableArray()
            }).ToImmutableArray() });
        var result = builder.Freeze(); var check = ExitChecker.Check(result);
        if (!check.IsValid) throw new InvalidOperationException("异常入口切块违反原生契约：" + string.Join("；", check.Violations));
        return result;
    }

}
