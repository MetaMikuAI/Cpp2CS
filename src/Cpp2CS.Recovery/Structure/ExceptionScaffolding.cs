using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Recovery.Structure;

/// <summary>托管包装假设下，私有 C++ 捕获操作不产生托管展开；先移去这些边及其不可达清理。</summary>
public static class ExceptionScaffolding
{
    public static NativeFunction Project(NativeFunction function, CallNamingQuery calls)
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
        return changed ? rewrite.Apply() : function;
    }
}
