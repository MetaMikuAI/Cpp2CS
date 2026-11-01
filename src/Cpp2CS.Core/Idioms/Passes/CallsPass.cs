using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class CallsPass
{
    internal static void Calls(this IdiomState state, bool indirectOnly = false)
    {
        foreach (var block in state.function.Blocks)
        {
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null } call)
                    continue;
                if (indirectOnly && call.Kind is not (CallKind.Indirect or CallKind.TailIndirect))
                    continue;
                var rewritten = call.Kind is CallKind.Indirect or CallKind.TailIndirect ? state.Indirect(call) : state.Direct(block, i, call);
                if (rewritten is null)
                    continue;
                // 虚调用：目标 = (*obj)->vtable[n].methodPtr，obj 为第一个参数
                if (state.recording && rewritten.Op is { Kind: OpKind.CallVirtual, Operand: int slot } && call.Kind == CallKind.Indirect && call.Arguments.Length > 0)
                {
                    var (where, at) = (block, state.Start(block, i, call.Target, call.Arguments[0]));
                    // 处于 try 区间的调用自成一块，目标在唯一前驱中计算：起点放到前驱里
                    if (at.Address == block.Start && block.Predecessors.Distinct().ToArray() is [var previous] && previous.NormalSuccessors.Count() == 1 && !block.IsLandingPad && state.Start(previous, previous.Statements.Count, call.Target, call.Arguments[0]) is var before && before.Index < previous.Statements.Count)
                        (where, at) = (previous, before);
                    if (state.Location(state.defs.Expand(call.Arguments[0]), where, at) is { } objectAt)
                        state.Record(Template.VirtualCall, where, at, new() { ["call"] = call.Address }, new() { ["object"] = objectAt, ["offset"] = (ulong)RuntimeLayout.ClassVtable + (ulong)slot * (ulong)RuntimeLayout.VirtualInvokeDataSize });
                }

                block.Statements[i] = rewritten;
            }
        }
    }
}
