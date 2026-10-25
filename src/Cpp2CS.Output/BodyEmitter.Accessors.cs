using Cpp2CS.Model;
using Cpp2CS.Recovery;
using Mono.Cecil.Cil;

namespace Cpp2CS.Output;

public sealed partial class BodyEmitter
{
    // 按指令记录认回点。普通代码中原有的同目标 call 仍然是可观察调用，不能一起变透明。
    public Dictionary<Instruction, FieldAccessor> AccessorCalls { get; } = [];
    /// <summary>内联认回的调用点（<see cref="ManagedCall.Inlined"/>）→ 被调方法；执行对照按被调方法体透明执行。</summary>
    public Dictionary<Instruction, MethodRef> InlineCalls { get; } = [];

    public string? AccessorDependencyProblem(MethodDef method) => AccessorDependencyEligibility.Problem(skeleton.Type(method.Owner));

    private string? AccessorProblem(ManagedValue value, bool write)
    {
        var accessor = value switch { FieldValue f => f.Accessor, StaticFieldValue f => f.Accessor, _ => null };
        if (accessor is null) return null;
        return accessor.Matches(types, accessContext, value, write) ? null : "访问权限 访问器证明与字段访问不符";
    }

    private void AccessorCall(FieldAccessor accessor)
    {
        var instruction = Instruction.Create(OpCodes.Call, MethodReference(accessor.Method));
        il.Append(instruction);
        AccessorCalls.Add(instruction, accessor);
    }
}
