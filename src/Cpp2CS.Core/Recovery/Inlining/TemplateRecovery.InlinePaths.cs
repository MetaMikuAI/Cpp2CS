using Cpp2CS.Ir;

namespace Cpp2CS.Recovery.Inlining;

internal sealed partial class TemplateRecovery
{
    /// <summary>沿唯一前驱链收集入口条件与已保存的读取；写入使可能别名的读取失效，调用截断链。</summary>
    private void SeedPath(Walker caller)
    {
        var chain = new List<ManagedBlock>();
        var seen = new HashSet<ulong> { caller.Block };
        var at = caller.Block;
        bool Trackable(ManagedStatement statement) => statement is ManagedJump or ManagedBranch or ManagedCheck
            || (statement is ManagedAssignment or ManagedStore { Target: FieldValue or StaticFieldValue or ArrayElementValue })
            && !ManagedValues.Of(statement).SelectMany(ManagedValues.Walk).Any(v => v is NewObjectValue or NewArrayValue or BoxValue or DelegateValue or HoleValue);
        if (caller.Blocks[at].Statements.Take(caller.Index).Any(s => !Trackable(s))) return;
        while (chain.Count < 16)
        {
            var predecessors = caller.Blocks.Values.Where(b => b.Statements.SelectMany(ManagedValues.Edges).Any(e => e.Target == at)).ToArray();
            if (predecessors is not [var predecessor] || !seen.Add(predecessor.Address) || predecessor.Statements.Any(s => !Trackable(s))) break;
            chain.Add(predecessor);
            at = predecessor.Address;
        }
        chain.Reverse();
        var walker = new Walker { Blocks = caller.Blocks, Caller = true, Block = at, Index = 0 };
        foreach (var block in chain.Append(caller.Blocks[caller.Block]))
        {
            var statements = block.Address == caller.Block ? block.Statements.Take(caller.Index) : block.Statements;
            foreach (var statement in statements)
            {
                if (statement is ManagedStore store && Location(walker, store.Target) is { } location)
                {
                    foreach (var variable in walker.Env.Where(p => ReadsLocation(p.Value, location)).Select(p => p.Key).ToArray()) walker.Env.Remove(variable);
                    caller.Assumptions.RemoveAll(p => ReadsLocation(p.Condition, location));
                }
                if (statement is ManagedAssignment assignment && Term(walker, assignment.Value) is { } value) walker.Env[assignment.Target.Variable] = value;
                if (statement is ManagedCheck check && Term(walker, check.Condition) is { } passed) caller.Assumptions.Add((passed, false));
                ManagedEdge? edge = null;
                if (statement is ManagedJump jump) edge = jump.Edge;
                if (statement is ManagedBranch branch)
                {
                    var next = chain.SkipWhile(b => b.Address != block.Address).Skip(1).FirstOrDefault()?.Address ?? caller.Block;
                    if ((branch.Taken.Target == next) == (branch.Fallthrough.Target == next)) continue;
                    var taken = branch.Taken.Target == next;
                    if (Term(walker, branch.Condition) is { } condition) caller.Assumptions.Add((condition, taken));
                    edge = taken ? branch.Taken : branch.Fallthrough;
                }
                if (edge is null) continue;
                var copied = edge.Copies.Select(c => (c.Target.Variable, Value: Term(walker, c.Value))).ToArray();
                foreach (var (variable, copiedValue) in copied)
                    if (copiedValue is not null) walker.Env[variable] = copiedValue;
            }
        }
        foreach (var (variable, value) in walker.Env) caller.Env[variable] = value;
    }

    private bool? KnownCondition(ManagedValue condition, Walker caller, IReadOnlyDictionary<int, ManagedValue> binding)
    {
        ManagedValue Bind(ManagedValue value) => value switch
        {
            ArgumentValue argument when binding.TryGetValue(argument.Index, out var bound) => bound,
            _ => MapTerm(value, Bind),
        };
        var instantiated = Bind(condition);
        if (instantiated is ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } comparison)
            return ConstantComparison(comparison.Condition, left, right);
        var canonical = CanonicalFact(instantiated);
        foreach (var assumption in caller.Assumptions)
        {
            if (SameTerm(canonical, CanonicalFact(assumption.Condition))) return assumption.Value;
            if (SameTerm(canonical, CanonicalFact(Negate(assumption.Condition)))) return !assumption.Value;
        }
        return null;
    }

    /// <summary>整数边界 x&lt;k 与 x&lt;=k-1 归一；边界不可递减时保留原式。</summary>
    private static ManagedValue CanonicalFact(ManagedValue value)
    {
        if (value is ComparisonValue { Right: ConstantValue constant } comparison && constant.Width is 8 or 16 or 32 or 64)
        {
            var bits = constant.Bits & Expr.Mask(constant.Width);
            var signed = comparison.Condition is Cond.Slt or Cond.Sge;
            if ((signed && bits != (1UL << (constant.Width - 1)) || !signed && bits != 0)
                && comparison.Condition is Cond.Slt or Cond.Sge or Cond.Ult or Cond.Uge)
                value = comparison with
                {
                    Condition = comparison.Condition switch { Cond.Slt => Cond.Sle, Cond.Sge => Cond.Sgt, Cond.Ult => Cond.Ule, _ => Cond.Ugt },
                    Right = constant with { Bits = (bits - 1) & Expr.Mask(constant.Width) },
                };
        }
        return Canonical(value);
    }
}
