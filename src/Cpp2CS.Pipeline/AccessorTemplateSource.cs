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

    public AccessorTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend)
    {
        var entries = facts.CodeMap.Entries.Where(e => e.Method is not null).GroupBy(e => e.Method!.Method)
            .ToDictionary(g => g.Key, g => g.OrderBy(e => e.Kind).ThenBy(e => e.Address).ThenBy(e => e.Index).First());
        var recovery = new IntegerRecoveryStage(enableAccessorInlining: false);
        templates = new(method =>
        {
            if (!method.DeclaresCilBody || !entries.TryGetValue(method, out var entry)) return null;
            var context = new MethodContext(method, entry, facts);
            return frontend.Run(entry, context) is Completed<NativeFunction> lifted
                && recovery.Run(lifted.Value, context) is Completed<ManagedBody> recovered ? recovered.Value : null;
        });
    }

    public AccessorTemplateResult Get(MethodDef method) => templates.Get(method);
}
