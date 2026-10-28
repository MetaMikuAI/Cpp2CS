using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Analysis;

namespace Cpp2CS.Recovery.Typing;

/// <summary>
/// 贡献者：按一种规则（签名、字段布局、类型检查、结构体、异常……）为函数产生约束。
/// 贡献者之间互不可见，只通过 <see cref="TypingContext.TypeOf"/> 读取上一轮的解（例如字段读取要等基址定型）。
/// 新的形态只需新增贡献者，不改引擎、不改其他贡献者。
/// </summary>
public interface ITypeContributor
{
    string Name { get; }
    void Contribute(TypingContext context, TypeConstraints constraints);
}

/// <summary>贡献者可用的输入：函数本身、入口参数的类型、调用解析、托管类型服务，以及上一轮的解。</summary>
public sealed class TypingContext(MachineFunction function, ManagedTypes types,
    IReadOnlyDictionary<Storage, TypeRef> entryTypes, Func<Call, MethodRef?> resolve)
{
    internal Dictionary<Variable, TypeResult> Solution { get; set; } = new();

    public MachineFunction Function { get; } = function;
    public ManagedTypes Types { get; } = types;
    /// <summary>入口寄存器（版本 0 变量）的托管类型，来自签名的 ABI 分类。</summary>
    public IReadOnlyDictionary<Storage, TypeRef> EntryTypes { get; } = entryTypes;
    /// <summary>调用的托管目标；依据不足时为 null。实现可以依赖 <see cref="TypeOf"/>（虚调用的接收者类型）。</summary>
    public Func<Call, MethodRef?> Resolve { get; } = resolve;

    /// <summary>上一轮推断出的托管类型。冲突时给出定义的下界（推导需要的事实不因使用处的冲突而消失）；未确定或运行时引用时为 null。</summary>
    public TypeRef? TypeOf(Variable v) => Solution.GetValueOrDefault(v) switch
    {
        ManagedResult m => m.Type,
        ConflictResult { Lower: { } lower } => lower,
        _ => null,
    };
    public bool IsRuntime(Variable v) => Solution.GetValueOrDefault(v) is RuntimeResult;

    public IEnumerable<Stmt> Statements => Function.Blocks.SelectMany(b => b.Statements);
}

/// <summary>
/// 轮流运行全部贡献者并求解，直到解不再变化。每轮从空约束重建：贡献者看到的是上一轮的完整解，推导出的约束只对
/// 这一轮的解成立，不能留到以后（例如"φ 来源被当作 φ 的类型使用"，φ 的类型在早期轮次可能比最终的窄）。
/// 冲突的变量仍向贡献者给出下界（<see cref="ConflictResult.Lower"/>），避免"冲突—类型消失—约束消失—类型恢复"的振荡。
/// 超过轮数上限视为不收敛，由调用者记洞。规则的顺序不影响结果。
/// </summary>
public sealed class TypeEngine(IReadOnlyList<ITypeContributor> contributors, int maxRounds = 16)
{
    public IReadOnlyList<ITypeContributor> Contributors { get; } = contributors;

    public (Dictionary<Variable, TypeResult> Solution, int Rounds, bool Converged) Run(TypingContext context)
    {
        var result = Iteration.Run(context.Solution, previous =>
        {
            context.Solution = previous;
            var constraints = new TypeConstraints();
            foreach (var contributor in Contributors) contributor.Contribute(context, constraints);
            return TypeSolver.Solve(constraints, context.Types);
        }, Same, maxRounds);
        context.Solution = result.Value;
        return (result.Value, result.Rounds, result.Status == IterationStatus.Stable);
    }

    private static bool Same(Dictionary<Variable, TypeResult> a, Dictionary<Variable, TypeResult> b) =>
        a.Count == b.Count && a.All(p => b.TryGetValue(p.Key, out var other) && Equals(p.Value, other));
}
