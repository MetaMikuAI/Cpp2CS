using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

internal sealed partial class CilBodyWriter
{
    // 按指令记录认回点。普通代码中原有的同目标 call 仍然是可观察调用，不能一起变透明。
    private Dictionary<Instruction, FieldAccessor> AccessorCalls => symbols.AccessorCalls;
    /// <summary>内联认回的调用点（<see cref="ManagedCall.Inlined"/>）→ 被调方法；执行对照按被调方法体透明执行。</summary>
    private Dictionary<Instruction, MethodRef> InlineCalls => symbols.InlineCalls;

    private void AccessorCall(FieldAccessor accessor)
    {
        var instruction = Instruction.Create(OpCodes.Call, MethodReference(accessor.Method));
        il.Append(instruction);
        AccessorCalls.Add(instruction, accessor);
    }
}
