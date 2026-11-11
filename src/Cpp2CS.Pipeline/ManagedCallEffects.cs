using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Naming;

namespace Cpp2CS.Pipeline;

/// <summary>绑定给出传出区大小；其余内存仍取未知上界，帧逃逸由状态模型统一判断。</summary>
public sealed class ManagedCallEffects(CallNamingQuery calls) : ICallEffectSource
{
    public Outcome<CallEffects> Get(QueryContext context, Call call)
    {
        var classified = context.Get(calls, call.Identity);
        if (!classified.IsSuccess) return classified.Propagate<CallEffects>();
        var candidates = classified.Value.Candidates;
        int? bytes = classified.Value.Kind == CallKind.Managed && candidates?.Candidates.Length == 1
            ? candidates.Candidates[0].Binding.Value?.Signature.Slots.StackSize : null;
        return Outcome<CallEffects>.Success(new(true, bytes, []));
    }
}
