using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Calls;

/// <summary>单方法的调用绑定、类型版本与候选诊断；提交的身份证据不随临时类型推断失效。</summary>
internal sealed class CallBindingState
{
    private readonly Dictionary<Call, CallBinding> bindings = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Call, CallResolution> resolutions = new(ReferenceEqualityComparer.Instance);
    public int TypeVersion { get; private set; }
    public IReadOnlyCollection<CallResolution> Resolutions => resolutions.Values;

    public void InvalidateTypes() => TypeVersion++;
    public CallResolution? Resolution(Call call) => resolutions.GetValueOrDefault(call);

    public MethodRef? Cached(Call call, int irVersion) => bindings.TryGetValue(call, out var binding)
        && (binding.Committed || binding.Version == TypeVersion && binding.IrVersion == irVersion) ? binding.Method : null;

    public void Commit(Call call, MethodRef method)
    {
        if (bindings.TryGetValue(call, out var previous) && previous.Committed
            && (!Equals(previous.Method, method) || NativeBindings.Key(previous.Method!) != NativeBindings.Key(method)))
            throw new InvalidOperationException($"调用 0x{call.Address:x} 的已提交身份冲突：{previous.Method} / {method}");
        bindings[call] = new(method, TypeVersion, Committed: true);
    }

    public void Candidates(Call call, ulong entry, IReadOnlyList<CallCandidate> candidates, MethodRef? selected, string status) =>
        resolutions[call] = new(call.Address, entry, TypeVersion, candidates, selected, status);

    public void Remember(Call call, MethodRef? method, int irVersion)
    {
        bindings[call] = new(method, TypeVersion, IrVersion: irVersion);
        if (!resolutions.TryGetValue(call, out var resolution) || resolution.TypeVersion != TypeVersion)
            resolutions[call] = new(call.Address, (call.Target as Const)?.Value, TypeVersion,
                method is null ? [] : [new(method, call.Op?.Kind.ToString() ?? "native-identity")], method, method is null ? "blocked" : "bound");
        else if (method is not null) resolutions[call] = resolution with { Selected = method };
    }

    public void Move(Call previous, Call replacement)
    {
        if (bindings.Remove(previous, out var binding)) bindings[replacement] = binding;
    }

    public void Copy(Call previous, Call replacement)
    {
        if (bindings.TryGetValue(previous, out var binding)) bindings[replacement] = binding;
        if (resolutions.TryGetValue(previous, out var resolution)) resolutions[replacement] = resolution;
    }
}
