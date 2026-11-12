using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；成功与失败均缓存，活动方法不提供递归截断体。</summary>
public sealed class MethodTemplateSource : IMethodTemplateSource
{
    private readonly object gate = new();
    private readonly Dictionary<MethodDef, StageResult<ManagedBody>> bodies = [];
    private readonly HashSet<MethodDef> active = [];
    private readonly Func<MethodDef, StageResult<ManagedBody>> recover;
    public MethodTemplateSource(GlobalFacts facts, IMethodStage<CodeEntry, NativeFunction> frontend, bool constructors)
    {
        var entries = facts.CodeMap.Entries.Where(e => e.Method is not null).GroupBy(e => e.Method!.Method)
            .ToDictionary(g => g.Key, g => RecoverySession.SelectEntry(g.Key, g));
        var recovery = new IntegerRecoveryStage(enableAccessorInlining: false, enableConstructorInlining: constructors, constructorSource: this);
        recover = method =>
        {
            if (!method.DeclaresCilBody) return Missing("inline.Template.NoBody", "候选声明没有托管方法体");
            if (!entries.TryGetValue(method, out var entry)) return Missing("inline.Template.NoEntry", "候选没有原生入口");
            if (GenericWitness.IsGeneric(method) && (entry.Kind != EntryKind.GenericMethod || entry.Method is null || !GenericWitness.IsCanonical(entry.Method)))
                return Missing("lowering.Generic.Witness", "候选没有全 object 的规范实例入口");
            var context = new MethodContext(method, entry, facts);
            return frontend.Run(entry, context) switch
            {
                Completed<NativeFunction> lifted => recovery.Run(lifted.Value, context),
                Missing<NativeFunction> missing => new Missing<ManagedBody>(missing.Hole),
                _ => throw new InvalidOperationException("未知的前端恢复结果"),
            };
        };
    }
    private static Missing<ManagedBody> Missing(string code, string message) => new(new("恢复", 0, "模板", new(code, message)));
    public ManagedBody? GetBody(MethodDef method) => Result(method) is Completed<ManagedBody> complete ? complete.Value : null;
    public Reason? GetFailure(MethodDef method) => Result(method) is Missing<ManagedBody> missing ? missing.Hole.Reason : null;
    private StageResult<ManagedBody> Result(MethodDef method)
    {
        lock (gate)
        {
            if (bodies.TryGetValue(method, out var body)) return body;
            if (!active.Add(method)) return Missing("inline.Template.Recursive", "候选恢复依赖活动中的模板");
            body = recover(method);
            active.Remove(method);
            bodies.Add(method, body);
            return body;
        }
    }
}
