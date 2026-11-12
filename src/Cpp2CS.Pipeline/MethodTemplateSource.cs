using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；成功与失败均缓存，活动方法不提供递归截断体。</summary>
public sealed class MethodTemplateSource : IMethodTemplateSource
{
    private readonly object gate = new();
    private readonly Dictionary<MethodDef, ManagedBody?> bodies = [];
    private readonly HashSet<MethodDef> active = [];
    private readonly Func<MethodDef, ManagedBody?> recover;
    public MethodTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend, bool constructors)
    {
        var entries = facts.CodeMap.Entries.Where(e => e.Method is not null).GroupBy(e => e.Method!.Method)
            .ToDictionary(g => g.Key, g => g.OrderBy(e => e.Kind).ThenBy(e => e.Address).ThenBy(e => e.Index).First());
        var recovery = new IntegerRecoveryStage(enableAccessorInlining: false, enableConstructorInlining: constructors, constructorSource: this);
        recover = method =>
        {
            if (!method.DeclaresCilBody || !entries.TryGetValue(method, out var entry)) return null;
            var context = new MethodContext(method, entry, facts);
            return frontend.Run(entry, context) is Completed<NativeFunction> lifted
                && recovery.Run(lifted.Value, context) is Completed<ManagedBody> recovered ? recovered.Value : null;
        };
    }
    public ManagedBody? GetBody(MethodDef method)
    {
        lock (gate)
        {
            if (bodies.TryGetValue(method, out var body)) return body;
            if (!active.Add(method)) return null;
            body = recover(method);
            active.Remove(method);
            bodies.Add(method, body);
            return body;
        }
    }
}
