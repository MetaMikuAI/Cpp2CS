using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Analysis;

/// <summary>
/// 一个方法的洞账本：各阶段登记独立洞、受影响的语句与变量，以及变量之间的数据流依赖；
/// 连带关系（毒化沿依赖边传播、派生洞指向最终的独立根因）都在这里计算，不再分散在恢复器的几套字典里。
/// </summary>
internal sealed class HoleLedger(Func<Stmt, IEnumerable<Variable>> definedBy)
{
    private readonly List<RecoveryHole> holes = [];
    private readonly Dictionary<Variable, RecoveryHole> poisoned = new();
    private readonly Dictionary<Variable, List<Variable>> dependents = new();
    private readonly Dictionary<Stmt, RecoveryHole> diagnosed = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<RecoveryHole, RecoveryHole> causes = new();
    private readonly List<(int Index, Variable Variable, Stmt? Statement)> unresolved = [];

    public IReadOnlyList<RecoveryHole> Holes => holes;
    public int Count => holes.Count;
    public IReadOnlyCollection<Variable> PoisonedVariables => poisoned.Keys;

    /// <summary>派生洞的文本：原因加上"源于"根因。</summary>
    public static string DerivedReason(RecoveryHole cause, string reason) => $"{reason}（源于 0x{cause.Address:x}：{cause.Reason}）";

    public RecoveryHole Add(ulong address, string reason, bool derived = false)
    {
        var hole = new RecoveryHole(address, reason, derived);
        holes.Add(hole);
        return hole;
    }

    /// <summary>hole 是由 cause 引起的派生洞；最终文本由 <see cref="Finish"/> 统一指向根因。</summary>
    public void Link(RecoveryHole hole, RecoveryHole cause) => causes[hole] = cause;

    /// <summary>"变量类型未定"的洞要等全部语句诊断完才知道根因：可能是后面的调用或回边上的另一个洞。</summary>
    public void Unresolved(Variable variable, Stmt? statement) => unresolved.Add((holes.Count - 1, variable, statement));

    public void Dependency(Variable source, Variable target)
    {
        if (!dependents.TryGetValue(source, out var users)) dependents[source] = users = [];
        users.Add(target);
    }

    /// <summary>依赖边建好之前已毒化的变量，沿依赖边补传一次。</summary>
    public void PropagateExisting()
    {
        foreach (var (source, cause) in poisoned.ToArray())
            if (dependents.TryGetValue(source, out var users))
                foreach (var user in users) Poison(user, cause);
    }

    public bool TryGetPoison(Variable variable, out RecoveryHole cause) => poisoned.TryGetValue(variable, out cause!);

    public void Poison(Variable variable, RecoveryHole cause)
    {
        var pending = new Queue<Variable>();
        pending.Enqueue(variable);
        while (pending.TryDequeue(out var next))
        {
            if (!poisoned.TryAdd(next, cause)) continue;
            if (dependents.TryGetValue(next, out var users))
                foreach (var user in users) pending.Enqueue(user);
        }
    }

    /// <summary>语句定义的全部变量（Define 的目标、调用结果，以及并入构造的分配结果）。</summary>
    public void Poison(Stmt statement, RecoveryHole cause)
    {
        foreach (var variable in definedBy(statement)) Poison(variable, cause);
    }

    /// <summary>语句已被某个洞诊断过（下降阶段遇到它时报派生洞）。同一语句只记第一个原因。</summary>
    public void Diagnose(Stmt statement, RecoveryHole hole) => diagnosed.TryAdd(statement, hole);

    /// <summary>诊断语句并毒化它定义的变量。</summary>
    public void Block(Stmt statement, RecoveryHole hole)
    {
        Diagnose(statement, hole);
        Poison(statement, hole);
    }

    public bool TryGetDiagnosis(Stmt statement, out RecoveryHole cause) => diagnosed.TryGetValue(statement, out cause!);

    /// <summary>语句被改写成新对象时，诊断随之转移。</summary>
    public void Replace(Stmt old, Stmt mapped)
    {
        if (diagnosed.Remove(old, out var cause)) diagnosed[mapped] = cause;
    }

    /// <summary>把全部派生洞指向最终的独立根因，"类型未定"的洞按最终的毒化情况归因。</summary>
    public void Finish()
    {
        RecoveryHole Root(RecoveryHole cause)
        {
            while (causes.TryGetValue(cause, out var parent)) cause = parent;
            return cause;
        }
        foreach (var (index, variable, statement) in unresolved)
        {
            var hole = holes[index];
            if (poisoned.TryGetValue(variable, out var cause) && Root(cause) is var root && root != hole)
                causes[hole] = root;
            else if (statement is Define) Poison(statement, hole);
        }
        // 回边和后续调用可能把临时的“类型未定”归到更早的根因；来源文本也统一指向最终独立洞。
        for (var i = 0; i < holes.Count; i++)
            if (causes.TryGetValue(holes[i], out var cause))
            {
                var reason = holes[i].Reason;
                var marker = reason.IndexOf("（源于 ", StringComparison.Ordinal);
                holes[i] = holes[i] with { Derived = true, Reason = DerivedReason(Root(cause), marker < 0 ? reason : reason[..marker]) };
            }
    }
}
