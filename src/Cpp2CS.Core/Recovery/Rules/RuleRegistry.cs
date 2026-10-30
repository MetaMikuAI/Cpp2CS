using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;
using System.Reflection;
using System.Linq.Expressions;

namespace Cpp2CS.Recovery;

internal static class RuleRegistry
{
    private const BindingFlags Members = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
    private static readonly MethodInfo[] Methods = typeof(RecoveryScope).Assembly.GetTypes().SelectMany(t => t.GetMethods(Members)).ToArray();
    public static readonly IReadOnlyDictionary<string, AnalysisInvalidation> MachinePasses = Methods
        .Select(m => m.GetCustomAttribute<MachinePassAttribute>()).OfType<MachinePassAttribute>().ToDictionary(a => a.Name, a => a.Invalidates);
    public static readonly (string Name, Func<RecoveryScope, RecoveryFailure?> Run)[] Analyses = OrderAnalyses();
    public static readonly Func<LoweringScope, Block, Stmt, List<ManagedStatement>, RecoveryResult<bool>>[] Statements = Rules<StatementRuleAttribute, Func<LoweringScope, Block, Stmt, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Define, List<ManagedStatement>, RecoveryResult<bool>>[] Defines = Rules<DefineRuleAttribute, Func<LoweringScope, Define, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Store, List<ManagedStatement>, RecoveryResult<bool>>[] Stores = Rules<StoreRuleAttribute, Func<LoweringScope, Store, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Store, ManagedValue, List<ManagedStatement>, RecoveryResult<bool>>[] StoreTargets = Rules<StoreTargetRuleAttribute, Func<LoweringScope, Store, ManagedValue, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>[] Calls = Rules<CallRuleAttribute, Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>[] Invocations = Rules<InvocationRuleAttribute, Func<LoweringScope, Call, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, RecoveryResult<bool>>[] InvocationOutputs = Rules<InvocationOutputRuleAttribute, Func<LoweringScope, Call, AbiSignature, Dictionary<Storage, Expr>, ManagedInvocation, List<ManagedStatement>, RecoveryResult<bool>>>(a => a.Order);
    public static readonly Func<LoweringScope, AbiValue, ArgumentSite, RecoveryResult<ManagedValue?>>[] Arguments = Rules<ArgumentRuleAttribute, Func<LoweringScope, AbiValue, ArgumentSite, RecoveryResult<ManagedValue?>>>(a => a.Order);
    public static readonly Func<LoweringScope, Call, AbiValue, RecoveryResult<LocalValue?>>[] Results = Rules<ResultRuleAttribute, Func<LoweringScope, Call, AbiValue, RecoveryResult<LocalValue?>>>(a => a.Order);
    public static readonly Func<RecoveryScope, AbiValue, int, bool>[] Parameters = Rules<ParameterBindingAttribute, Func<RecoveryScope, AbiValue, int, bool>>(a => a.Order);
    public static readonly Action<RecoveryScope, ManagedBody>[] Proofs = Rules<BodyProofAttribute, Action<RecoveryScope, ManagedBody>>(a => a.Order);
    private static TDelegate[] Rules<TAttribute, TDelegate>(Func<TAttribute, int> order)
        where TAttribute : Attribute where TDelegate : Delegate => Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<TAttribute>())).Where(p => p.Attribute is not null).OrderBy(p => order(p.Attribute!)).ThenBy(p => p.Method.Name, StringComparer.Ordinal).Select(p => Adapt<TDelegate>(p.Method)).ToArray();
    private static TDelegate Adapt<TDelegate>(MethodInfo method)
        where TDelegate : Delegate
    {
        var signature = typeof(TDelegate).GetMethod("Invoke")!;
        var arguments = signature.GetParameters().Select(p => Expression.Parameter(p.ParameterType, p.Name)).ToArray();
        var call = Expression.Call(method, arguments);
        Expression result = method.ReturnType == typeof(void) && signature.ReturnType != typeof(void) ? Expression.Block(call, Expression.Default(signature.ReturnType)) : method.ReturnType == signature.ReturnType ? call : Expression.Convert(call, signature.ReturnType);
        return Expression.Lambda<TDelegate>(result, arguments).Compile();
    }

    /// <summary>拓扑排序：After 中的步骤必须已经运行；可运行的步骤中先运行 Order 最小的。缺少依赖或成环时启动即失败。</summary>
    private static (string, Func<RecoveryScope, RecoveryFailure?>)[] OrderAnalyses()
    {
        var steps = Methods.Select(m => (Method: m, Attribute: m.GetCustomAttribute<AnalysisAttribute>())).Where(p => p.Attribute is not null).ToDictionary(p => p.Attribute!.Name, p => (p.Attribute!, Run: Adapt<Func<RecoveryScope, RecoveryFailure?>>(p.Method)));
        foreach (var (name, (attribute, _)) in steps)
            foreach (var dependency in attribute.After)
                if (!steps.ContainsKey(dependency))
                    throw new InvalidOperationException($"分析 {name} 依赖未注册的分析 {dependency}");
        var done = new HashSet<string>();
        var ordered = new List<(string, Func<RecoveryScope, RecoveryFailure?>)>();
        while (ordered.Count < steps.Count)
        {
            var next = steps.Where(p => !done.Contains(p.Key) && p.Value.Item1.After.All(done.Contains)).OrderBy(p => p.Value.Item1.Order).ThenBy(p => p.Key, StringComparer.Ordinal).Select(p => p.Key).FirstOrDefault() ?? throw new InvalidOperationException("分析的依赖成环：" + string.Join("、", steps.Keys.Where(k => !done.Contains(k))));
            done.Add(next);
            ordered.Add((next, steps[next].Run));
        }

        return ordered.ToArray();
    }
}
