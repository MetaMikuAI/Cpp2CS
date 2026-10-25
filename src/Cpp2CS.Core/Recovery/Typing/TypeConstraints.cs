using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Recovery.Typing;

/// <summary>一条约束的来源：贡献者、机器地址与说明。冲突时原样写进洞的原因，便于追溯是哪两条规则相互矛盾。</summary>
public sealed record TypeEvidence(string Contributor, ulong Address, string Detail)
{
    public override string ToString() => $"{Contributor}@0x{Address:x}（{Detail}）";
}

/// <summary>运行时引用的种类（klass、MethodInfo、VirtualInvokeData、RGCTX……）。它们不是托管值，不能出现在托管语句里。</summary>
public sealed record RuntimeKind(string Name);

/// <summary>
/// 一轮推断收集到的全部约束。三种基本关系：
/// 定义（下界：值至少是这个类型）、流（φ 与复制：目标的下界包含来源的下界）、使用（上界：值必须能当作这个类型使用）；
/// 另有运行时引用的标记。贡献者只往这里加约束，不读写其他贡献者的状态。
/// </summary>
public sealed class TypeConstraints
{
    internal Dictionary<Variable, HashSet<(TypeRef Type, TypeEvidence Evidence)>> Definitions { get; } = new();
    internal Dictionary<Variable, HashSet<(Variable Source, TypeEvidence Evidence)>> FlowEdges { get; } = new();
    internal Dictionary<Variable, HashSet<(TypeRef Type, TypeEvidence Evidence)>> Uses { get; } = new();
    internal Dictionary<Variable, HashSet<(RuntimeKind Kind, TypeEvidence Evidence)>> Runtime { get; } = new();
    internal Dictionary<Variable, HashSet<TypeEvidence>> Clobbered { get; } = new();

    /// <summary>v 的值由定义产生，类型至少精确到 type：参数、调用结果、字段读取、分配等。</summary>
    public void Defines(Variable v, TypeRef type, TypeEvidence evidence) => _ = Add(Definitions, v, (type, evidence));

    /// <summary>to 的值来自 from（φ 的来源、复制）。</summary>
    public void Flows(Variable from, Variable to, TypeEvidence evidence) => _ = Add(FlowEdges, to, (from, evidence));

    /// <summary>v 被当作 type 使用：实参、写入的值、返回值、接收者等，要求 v 的类型可赋给 type。</summary>
    public void Requires(Variable v, TypeRef type, TypeEvidence evidence) => _ = Add(Uses, v, (type, evidence));

    /// <summary>v 是运行时引用，不是托管值。</summary>
    public void IsRuntime(Variable v, RuntimeKind kind, TypeEvidence evidence) => _ = Add(Runtime, v, (kind, evidence));

    /// <summary>v 没有值：调用破坏的寄存器版本（调用写入、但不是 ABI 返回片）。它不参与汇合；真正被使用时由下降阶段留洞。</summary>
    public void IsClobbered(Variable v, TypeEvidence evidence) => _ = Add(Clobbered, v, evidence);

    internal IEnumerable<Variable> Variables =>
        Definitions.Keys.Concat(FlowEdges.Keys).Concat(FlowEdges.Values.SelectMany(l => l.Select(f => f.Source))).Concat(Uses.Keys).Concat(Runtime.Keys).Concat(Clobbered.Keys).Distinct();

    private static bool Add<T>(Dictionary<Variable, HashSet<T>> map, Variable v, T item)
    {
        if (!map.TryGetValue(v, out var set)) map[v] = set = [];
        return set.Add(item);
    }
}

/// <summary>推断结果。没有结果的变量表示约束不足（类型未确定）。</summary>
public abstract record TypeResult;
public sealed record ManagedResult(TypeRef Type) : TypeResult;
public sealed record RuntimeResult(RuntimeKind Kind) : TypeResult;
/// <summary>没有值（调用破坏的寄存器）。不是"未知"：再多的证据也不会让它有类型。</summary>
public sealed record ClobberedResult(TypeEvidence Evidence) : TypeResult;
/// <summary>约束相互矛盾。Reason 列出矛盾双方的来源；Lower 是定义给出的下界（有时），只供下一轮的贡献者推导，不进入最终结果。</summary>
public sealed record ConflictResult(string Reason, TypeRef? Lower = null) : TypeResult;
