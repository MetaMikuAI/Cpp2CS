using Cpp2CS.Ir;
using Cpp2CS.Recovery.Typing;

namespace Cpp2CS.Recovery.Lowering;

internal sealed partial class BodyBuilder
{
    /// <summary>内联方法的返回值直接参与比较时，证明各路径分别到达同一对条件出口。</summary>
    private bool ConcludePredicate(InlineMatch match, MethodRef method, IReadOnlyDictionary<ulong, ManagedBlock> blocks)
    {
        if (ManagedTypes.IsVoid(method.Method.ReturnType) || match.Ends.Count == 0 || match.Ends.Any(e => e.Returns)) return false;
        var returnType = TypeOracle.Concrete(method, method.Method.ReturnType);
        if (types.Kind(returnType) is not (TypeKind.Int or TypeKind.Bool)) return false;
        Walker At(InlineEnd end) => new() { Blocks = blocks, Caller = true, Block = end.Exit.Block, Index = end.Exit.Index, Env = new(end.Env) };
        ComparisonValue? predicate = null;
        var result = NewLocal(returnType);
        foreach (var end in match.Ends)
        {
            var walker = At(end);
            if (end.Result is not { } returned || returned is ConstantValue || walker.Current is not ManagedBranch branch || Term(walker, branch.Condition) is not ComparisonValue comparison) continue;
            if (comparison.Left.Equals(returned) && comparison.Right is ConstantValue) predicate = comparison with { Left = result };
            else if (comparison.Right.Equals(returned) && comparison.Left is ConstantValue) predicate = comparison with { Right = result };
            if (predicate is not null) break;
        }
        if (predicate is null) return false;
        ManagedValue Apply(ManagedValue value) => ManagedValues.Map(predicate, child => child.Equals(result) ? value : child);
        var exits = new Dictionary<bool, InlineEnd>();
        var covered = new HashSet<(ulong Block, int Index)>();
        bool Note(bool outcome, InlineEnd end)
        {
            if (end.Exit.Index != 0) return match.Fail("条件续接点位于块中间");
            var copies = end.Copies.GroupBy(c => c.Target.Variable).Select(g => g.Last()).ToArray();
            end = end with { Copies = copies };
            if (exits.TryGetValue(outcome, out var prior))
            {
                if (prior.Exit != end.Exit) return match.Fail("相同返回条件的续接点不同");
                var targets = prior.Copies.Select(c => c.Target).Concat(end.Copies.Select(c => c.Target)).DistinctBy(l => l.Variable).ToArray();
                ManagedValue? Held(InlineEnd e, LocalValue target) => e.Copies.FirstOrDefault(c => c.Target.Variable.Equals(target.Variable)).Value ?? e.Env.GetValueOrDefault(target.Variable);
                if (targets.Any(t => Held(prior, t) is not { } value || Held(end, t) is not { } other || !SameTerm(value, other))) return match.Fail("条件续接的局部值不同");
                exits[outcome] = end with { Copies = targets.Select(t => (t, Held(end, t)!)).ToArray() };
                return true;
            }
            exits[outcome] = end;
            return true;
        }
        bool Along(InlineEnd end, ManagedEdge edge, bool outcome)
        {
            var walker = At(end);
            var copies = end.Copies.ToList();
            foreach (var copy in edge.Copies)
            {
                if (Term(walker, copy.Value) is not { } value) return false;
                copies.Add((copy.Target, value));
            }
            if (!Follow(walker, edge)) return false;
            var trial = new InlineMatch { Binding = [], TypeArguments = match.TypeArguments };
            if (!Finish(walker, trial, null) || trial.Ends.Count != 1) return false;
            covered.UnionWith(trial.Covered);
            var finish = trial.Ends[0];
            return Note(outcome, finish with { Copies = copies.Concat(finish.Copies).ToArray() });
        }
        foreach (var end in match.Ends)
        {
            if (end.Result is not { } returned) return false;
            var expected = Apply(returned);
            var walker = At(end);
            if (expected is ComparisonValue { Left: ConstantValue left, Right: ConstantValue right } constant
                && ConstantComparison(constant.Condition, left, right) is { } outcome)
            {
                if (!Note(outcome, end)) return false;
            }
            else if (walker.Current is ManagedBranch branch && Term(walker, branch.Condition) is { } condition)
            {
                var canonical = Canonical(expected);
                bool same;
                if (Unify(canonical, Canonical(condition), match.Binding)) same = true;
                else if (Unify(canonical, Canonical(Negate(condition)), match.Binding)) same = false;
                else return match.Fail("返回值与调用方的比较不同");
                covered.Add(end.Exit);
                if (!Along(end, branch.Taken, same) || !Along(end, branch.Fallthrough, !same)) return false;
            }
            else return match.Fail("返回路径不受同一条件支配");
        }
        if (!exits.TryGetValue(true, out var yes) || !exits.TryGetValue(false, out var no) || yes.Exit == no.Exit) return false;
        ManagedEdge Edge(InlineEnd end) => new(end.Exit.Block, end.Copies.Select(c => new ManagedCopy(c.Target, c.Value)).ToArray());
        match.Covered.UnionWith(covered);
        match.Result = result;
        match.Exit = yes.Exit;
        match.ExitCopies = [];
        match.Continuation = new ManagedBranch(0, predicate, Edge(yes), Edge(no));
        return true;
    }

    private static bool? ConstantComparison(Cond condition, ConstantValue left, ConstantValue right)
    {
        if (left.Width != right.Width || left.Width is not (8 or 16 or 32 or 64)) return null;
        var a = left.Bits & Expr.Mask(left.Width);
        var b = right.Bits & Expr.Mask(right.Width);
        var sign = 1UL << (left.Width - 1);
        return condition switch
        {
            Cond.Eq => a == b, Cond.Ne => a != b,
            Cond.Ult => a < b, Cond.Ule => a <= b, Cond.Ugt => a > b, Cond.Uge => a >= b,
            Cond.Slt => (a ^ sign) < (b ^ sign), Cond.Sle => (a ^ sign) <= (b ^ sign),
            Cond.Sgt => (a ^ sign) > (b ^ sign), Cond.Sge => (a ^ sign) >= (b ^ sign),
            _ => null,
        };
    }
}
