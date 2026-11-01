using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using System.Reflection;
using System.Linq.Expressions;

namespace Cpp2CS.Recovery;

/// <summary>一个已注册的步骤：Id、中文名、种类、失效声明与适配后的入口；<see cref="CanFail"/> 表示方法返回 RecoveryFailure?。</summary>
internal sealed record RegisteredStep(string Id, string Name, StepKind Kind, AnalysisInvalidation Invalidates, StepRefresh Refresh, bool CanFail, Func<RecoveryScope, RecoveryFailure?> Run);

/// <summary>一个已注册的 Prepare 步骤；<see cref="CanStop"/> 表示方法返回 PrepareOutcome。</summary>
internal sealed record RegisteredPrepareStep(string Id, StepKind Kind, bool CanStop, Func<RecoveryScope, PreparedMethod, PrepareOutcome> Run);

internal static class RuleRegistry
{
    private const BindingFlags Members = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
    private static readonly MethodInfo[] Methods = typeof(RecoveryScope).Assembly.GetTypes().SelectMany(t => t.GetMethods(Members)).ToArray();
    public static readonly RegisteredStep[] Analyses = OrderSteps(StepPhase.Analyze);
    private static readonly IReadOnlyDictionary<string, RegisteredStep> StepsById = Analyses.ToDictionary(s => s.Id, StringComparer.Ordinal);
    /// <summary>Prepare 阶段的步骤，按 Id；顺序由 <see cref="PreparePlan"/> 给出。</summary>
    public static readonly IReadOnlyDictionary<string, RegisteredPrepareStep> Prepares = Methods
        .Select(m => (Method: m, Attribute: m.GetCustomAttribute<StepAttribute>())).Where(p => p.Attribute?.Phase == StepPhase.Prepare)
        .ToDictionary(p => p.Attribute!.Id, p => new RegisteredPrepareStep(p.Attribute!.Id, p.Attribute.Kind, p.Method.ReturnType == typeof(PrepareOutcome), AdaptPrepare(p.Method)), StringComparer.Ordinal);
    public static readonly Func<LoweringScope, Block, Stmt, List<ManagedStatement>, RecoveryResult<bool>>[] Statements = Rules<Func<LoweringScope, Block, Stmt, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.Statement);
    public static readonly Func<LoweringScope, Define, List<ManagedStatement>, RecoveryResult<bool>>[] Defines = Rules<Func<LoweringScope, Define, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.Define);
    public static readonly Func<LoweringScope, Store, List<ManagedStatement>, RecoveryResult<bool>>[] Stores = Rules<Func<LoweringScope, Store, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.Store);
    public static readonly Func<LoweringScope, Store, ManagedValue, List<ManagedStatement>, RecoveryResult<bool>>[] StoreTargets = Rules<Func<LoweringScope, Store, ManagedValue, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.StoreTarget);
    public static readonly Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>[] Calls = Rules<Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.Call);
    public static readonly Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>[] Invocations = Rules<Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.Invocation);
    public static readonly Func<LoweringScope, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, RecoveryResult<bool>>[] InvocationOutputs = Rules<Func<LoweringScope, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, RecoveryResult<bool>>>(RuleKind.InvocationOutput);
    public static readonly Func<LoweringScope, AbiValue, ArgumentSite, RecoveryResult<ManagedValue?>>[] Arguments = Rules<Func<LoweringScope, AbiValue, ArgumentSite, RecoveryResult<ManagedValue?>>>(RuleKind.Argument);
    public static readonly Func<LoweringScope, Call, AbiValue, RecoveryResult<LocalValue?>>[] Results = Rules<Func<LoweringScope, Call, AbiValue, RecoveryResult<LocalValue?>>>(RuleKind.Result);
    public static readonly Func<RecoveryScope, AbiValue, int, bool>[] Parameters = Rules<Func<RecoveryScope, AbiValue, int, bool>>(RuleKind.ParameterBinding);
    public static readonly Action<RecoveryScope, ManagedBody>[] Proofs = Rules<Action<RecoveryScope, ManagedBody>>(RuleKind.BodyProof);

    /// <summary>按 Id 取已注册的步骤（维护动作的重跑用）。</summary>
    public static RegisteredStep Step(string id) => StepsById.TryGetValue(id, out var step) ? step : throw new InvalidOperationException($"未注册的步骤 {id}");

    static RuleRegistry() => CheckIds();

    /// <summary>Id 全局唯一（步骤与规则共用一个命名空间）；重复时启动即失败。</summary>
    private static void CheckIds()
    {
        var ids = new Dictionary<string, MethodInfo>(StringComparer.Ordinal);
        foreach (var method in Methods)
        {
            var id = method.GetCustomAttribute<StepAttribute>()?.Id ?? method.GetCustomAttribute<RuleAttribute>()?.Id;
            if (id is null)
                continue;
            if (!ids.TryAdd(id, method))
                throw new InvalidOperationException($"注册 Id 重复：{id}（{ids[id].DeclaringType!.Name}.{ids[id].Name}、{method.DeclaringType!.Name}.{method.Name}）");
        }
    }

    /// <summary>一个类别的规则按 Order 排列；类别内 Order 重复时启动即失败。</summary>
    private static TDelegate[] Rules<TDelegate>(RuleKind kind)
        where TDelegate : Delegate
    {
        var rules = Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<RuleAttribute>())).Where(p => p.Attribute?.Kind == kind).ToArray();
        foreach (var group in rules.GroupBy(p => p.Attribute!.Order).Where(g => g.Count() > 1))
            throw new InvalidOperationException($"{kind} 规则的 Order {group.Key} 重复：{string.Join("、", group.Select(p => p.Attribute!.Id))}");
        return rules.OrderBy(p => p.Attribute!.Order).Select(p => Adapt<TDelegate>(p.Method)).ToArray();
    }

    /// <summary>Prepare 步骤的适配：参数为作用域，可选地再接 PreparedMethod；其余可选参数取默认值；void 视为继续。</summary>
    private static Func<RecoveryScope, PreparedMethod, PrepareOutcome> AdaptPrepare(MethodInfo method)
    {
        var scope = Expression.Parameter(typeof(RecoveryScope), "scope");
        var prepared = Expression.Parameter(typeof(PreparedMethod), "prepared");
        var arguments = method.GetParameters().Select((p, i) => i == 0 && p.ParameterType == typeof(RecoveryScope) ? scope
            : p.ParameterType == typeof(PreparedMethod) ? (Expression)prepared
            : p.HasDefaultValue ? Expression.Constant(p.DefaultValue, p.ParameterType)
            : throw new InvalidOperationException($"Prepare 步骤 {method.DeclaringType!.Name}.{method.Name} 的参数 {p.Name} 无法提供")).ToArray();
        var call = Expression.Call(method, arguments);
        Expression body = method.ReturnType == typeof(PrepareOutcome) ? call
            : method.ReturnType == typeof(void) ? Expression.Block(call, Expression.Constant(PrepareOutcome.Continue))
            : throw new InvalidOperationException($"Prepare 步骤 {method.DeclaringType!.Name}.{method.Name} 的返回类型须为 void 或 PrepareOutcome");
        return Expression.Lambda<Func<RecoveryScope, PreparedMethod, PrepareOutcome>>(body, scope, prepared).Compile();
    }

    private static TDelegate Adapt<TDelegate>(MethodInfo method)
        where TDelegate : Delegate
    {
        var signature = typeof(TDelegate).GetMethod("Invoke")!;
        var arguments = signature.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
        var call = Expression.Call(method, arguments);
        Expression result = method.ReturnType == typeof(void) && signature.ReturnType != typeof(void) ? Expression.Block(call, Expression.Default(signature.ReturnType)) : method.ReturnType == signature.ReturnType ? call : Expression.Convert(call, signature.ReturnType);
        return Expression.Lambda<TDelegate>(result, arguments).Compile();
    }

    /// <summary>
    /// 拓扑排序：After 中的步骤必须已经运行；可运行的步骤中先运行 Order 最小的。阶段内 Order 唯一，所以顺序完全由 Order 与 After 决定。
    /// 缺少依赖、Order 重复或成环时启动即失败。
    /// </summary>
    private static RegisteredStep[] OrderSteps(StepPhase phase)
    {
        var steps = Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<StepAttribute>())).Where(p => p.Attribute?.Phase == phase)
            .ToDictionary(p => p.Attribute!.Id, p => (p.Attribute!, p.Method), StringComparer.Ordinal);
        foreach (var group in steps.Values.GroupBy(s => s.Item1.Order).Where(g => g.Count() > 1))
            throw new InvalidOperationException($"{phase} 阶段的步骤 Order {group.Key} 重复：{string.Join("、", group.Select(s => s.Item1.Id))}");
        foreach (var (id, (attribute, _)) in steps)
            foreach (var dependency in attribute.After)
                if (!steps.ContainsKey(dependency))
                    throw new InvalidOperationException($"步骤 {id} 依赖未注册的步骤 {dependency}");
        var done = new HashSet<string>(StringComparer.Ordinal);
        var ordered = new List<RegisteredStep>();
        while (ordered.Count < steps.Count)
        {
            var next = steps.Where(p => !done.Contains(p.Key) && p.Value.Item1.After.All(done.Contains)).OrderBy(p => p.Value.Item1.Order).Select(p => p.Key).FirstOrDefault()
                ?? throw new InvalidOperationException("步骤的依赖成环：" + string.Join("、", steps.Keys.Where(k => !done.Contains(k))));
            done.Add(next);
            var (attribute, method) = steps[next];
            ordered.Add(new(next, attribute.Name, attribute.Kind, attribute.Invalidates, attribute.Refresh, method.ReturnType != typeof(void),
                Adapt<Func<RecoveryScope, RecoveryFailure?>>(method)));
        }

        return ordered.ToArray();
    }
}
