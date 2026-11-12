using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；关闭内联逆，深度固定为一。</summary>
public sealed class AccessorTemplateSource : IAccessorTemplateSource
{
    private readonly CachedAccessorTemplates templates;
    private readonly MethodTemplateSource source;

    public AccessorTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend)
    {
        source = new MethodTemplateSource(facts, frontend, constructors: false);
        templates = new(source.GetBody);
    }

    public AccessorTemplateResult Get(MethodDef method)
    {
        var result = templates.Get(method);
        return result.Status == AccessorTemplateStatus.Incomplete ? result with { Failure = source.GetFailure(method) } : result;
    }
}
