using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery.Calls;

/// <summary>清理辅助函数已证明等价于托管清理方法时，按原生接收者解引用链改写调用，使局部内存能按真实用途提升。</summary>
internal static class CleanupCalls
{
    internal static int Run(MachineFunction function, Func<ulong, (MethodRef Method, int Depth, bool Inlined)?> prove)
    {
        var changed = 0;
        foreach (var block in function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Resolved: null, Kind: CallKind.Direct, Target: Const target } call
                    || call.ArgumentIndex(Storage.Gpr(0)) is not (>= 0 and var input) || prove(target.Value) is not { } proof) continue;
                Expr receiver = call.Arguments[input];
                for (var depth = 0; depth < proof.Depth; depth++) receiver = new Load(receiver, 64);
                block.Statements[i] = call with
                {
                    Resolved = proof.Method, Inlined = proof.Inlined,
                    Arguments = [receiver], Sources = [Storage.Gpr(0)],
                };
                changed++;
            }
        return changed;
    }
}
