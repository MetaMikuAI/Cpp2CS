using System.Collections.Concurrent;
using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；关闭内联逆，深度固定为一。</summary>
public sealed class AccessorTemplateSource : IAccessorTemplateSource
{
    private readonly CachedAccessorTemplates templates;
    private readonly MethodTemplateSource source;
    private readonly ClosedTemplateWitnesses witnesses;
    private readonly ConcurrentDictionary<MethodRef, Lazy<AccessorTemplateResult>> closed = [];

    public AccessorTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend)
    {
        source = new MethodTemplateSource(facts, frontend, constructors: false);
        templates = new(source.GetBody);
        witnesses = new(facts);
    }

    public AccessorTemplateResult Get(MethodDef method)
    {
        var result = templates.Get(method);
        return result.Status == AccessorTemplateStatus.Incomplete ? result with { Failure = source.GetFailure(method) } : result;
    }

    public AccessorTemplateResult Get(MethodRef method)
    {
        if (!AccessorTemplates.UsesClosedWitness(method.Method)) return Get(method.Method);
        var selected = witnesses.Select(method, "inline.Accessor.Witness");
        if (selected.Method is not { } witness) return new(AccessorTemplateStatus.Incomplete, Failure: selected.Failure);
        var evidence = selected.Evidence!;
        var result = closed.GetOrAdd(witness, m => new(() => source.GetBody(m) is { } body
            ? AccessorTemplates.ReadSingleField(body)
            : new(AccessorTemplateStatus.Incomplete, Failure: source.GetFailure(m)))).Value;
        return result with { Witness = evidence, Failure = result.Failure is { } failure
            ? failure with { Cause = evidence with { Cause = failure.Cause } } : null };
    }

}
