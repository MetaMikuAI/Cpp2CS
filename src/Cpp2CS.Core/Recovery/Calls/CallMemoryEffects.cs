using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Storage;
using Cpp2CS.Recovery.Effects;
using Cpp2CS.Recovery.Runtime;

namespace Cpp2CS.Recovery.Calls;

/// <summary>按调用形状与运行时操作表回答调用对帧内存的影响；目标未确定时保守。</summary>
/// <param name="settled">调用目标的解析已结束：仍未解析的调用只会成为洞，不再需要为它保留可能的栈实参。</param>
internal sealed class CallMemoryEffects(Func<Call, CallShape> shapes, ManagedAbi abi, bool settled = false) : IFrameCallEffects
{
    public ArgumentUse Argument(Call call, int index)
    {
        var shape = shapes(call);
        if (call.Op is { } op && shape.IsRuntime)
        {
            if (RuntimeOps.Of(op.Kind) is not { } rule) return ArgumentUse.Unknown;
            foreach (var effect in rule.PointerEffects?.Invoke(call, abi) ?? [])
                if (effect.Argument == index) return new(effect.Size, effect.Access, false);
            // 操作会读内存但这里给不出范围（类操作数尚未确定）时，实参可能被读取，不能当作不访问。
            if (rule.Behavior.InvalidatesMemory) return ArgumentUse.Unknown;
            return (rule.Behavior.Kinds & EffectKind.Read) != 0 ? new(-1, MemoryAccess.Read, false) : ArgumentUse.None;
        }
        foreach (var value in shape.Signature?.Indirections ?? [])
            if (call.ArgumentIndex(value.Pieces[0].Register) == index) return new(value.Size, value.Access, false);
        // 按引用类型传递的栈地址只能是栈上临时对象：codegen 保证它只在这次调用期间存在，调用不改写它。
        foreach (var value in shape.Signature?.Arguments ?? [])
            if (value.Transfer == Transfer.Value && ManagedTypes.IsReferenceType(value.Type) && call.ArgumentIndex(value.Pieces[0].Register) == index)
                return new(-1, MemoryAccess.Read, false);
        return ArgumentUse.Unknown;
    }

    public bool WritesEscaped(Call call) => call.Op is not { } op || !shapes(call).IsRuntime
        || RuntimeOps.Of(op.Kind)?.Behavior.InvalidatesMemory != false;

    public int? StackRead(Call call)
    {
        var shape = shapes(call);
        if (call.Op is { Kind: not (OpKind.Import or OpKind.Export) } && shape.IsRuntime) return 0;
        return shape.Signature?.StackSize ?? (settled ? 0 : null);
    }
}
