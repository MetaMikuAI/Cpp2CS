using Cpp2CS.Input;
using Cpp2CS.Managed;
using Cpp2CS.Model;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Inlining;

namespace Cpp2CS.Pipeline;

/// <summary>候选用同一全局事实和前端独立恢复；成功与失败均缓存，活动方法不提供递归截断体。不同候选可以并行恢复：只缓存完成的结果，递归按线程判断，两个线程同时要同一个候选时各算一次、结果相同。</summary>
public sealed class MethodTemplateSource : IMethodTemplateSource
{
    // Reentered：当前这一层恢复期间被重入的活动方法里最外一层的栈位置；没有重入时是 int.MaxValue。
    private sealed class Activity { public List<MethodDef> Active { get; } = []; public int Reentered = int.MaxValue; }
    private readonly System.Collections.Concurrent.ConcurrentDictionary<MethodDef, StageResult<ManagedBody>> bodies = new();
    private readonly ThreadLocal<Activity> activity = new(() => new());
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
        if (bodies.TryGetValue(method, out var body)) return body;
        var mine = activity.Value!;
        int active = mine.Active.IndexOf(method);
        if (active >= 0)
        {
            mine.Reentered = Math.Min(mine.Reentered, active);
            return Missing("inline.Template.Recursive", "候选恢复依赖活动中的模板");
        }
        int level = mine.Active.Count, outer = mine.Reentered;
        mine.Active.Add(method); mine.Reentered = int.MaxValue;
        try { body = recover(method); }
        finally { mine.Active.RemoveAt(level); }
        int reentered = mine.Reentered;
        // 环上的方法（恢复期间重入了自己或仍在活动的外层）读到了截断，不提供模板。
        // 截断只算在环上：重入的是自己时环在自己之内，外层读到的是这个方法的最终结果，不受牵连。
        mine.Reentered = Math.Min(outer, reentered < level ? reentered : int.MaxValue);
        if (reentered != int.MaxValue) body = Missing("inline.Template.Recursive", "候选恢复读取了递归截断，不能提供完整模板");
        return bodies.GetOrAdd(method, body);
    }
}
