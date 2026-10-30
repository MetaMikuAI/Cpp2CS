using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>捕获对象判空后，按同一组 phi 的来源判断清理状态分支，排除互不相容的路径。</summary>
internal static class ExceptionNullBranches
{
    public static bool Run(ProgramFacts facts, MachineFunction function)
    {
        var layout = ExceptionRegionBuilder.Build(facts, function);
        if (!layout.Succeeded) return false;
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = function.Blocks.SelectMany(b => b.Statements.OfType<Phi>().Select(p => (Phi: p, Block: b))).ToDictionary(p => p.Phi.Target);
        var wrappers = layout.Regions.Where(r => r.Kind == "catch").SelectMany(r => r.Handler.SelectMany(f => f.Statements)).OfType<Call>()
            .Where(c => c.Op?.Kind == OpKind.BeginCatch).SelectMany(c => c.Defines.OfType<Variable>()).ToHashSet();
        var nonNull = new HashSet<Variable>();
        for (var changed = true; changed;)
        {
            changed = false;
            foreach (var (variable, value) in definitions)
            {
                if (value is Use copy && wrappers.Contains(copy.Variable)) changed |= wrappers.Add(variable);
                if (value is Load { Width: 64, Address: Use address } && wrappers.Contains(address.Variable)
                    || value is Use alias && nonNull.Contains(alias.Variable)) changed |= nonNull.Add(variable);
            }
            foreach (var (phi, _) in phis.Values)
                if (phi.Sources.Any(nonNull.Contains) && phi.Sources.All(v => v == phi.Target || nonNull.Contains(v))) changed |= nonNull.Add(phi.Target);
        }
        Expr Expand(Expr expression, Block? block, int incoming, HashSet<Variable> active)
        {
            return Fold.Simplify(ExprMap.Map(expression, e =>
            {
                if (e is not Use use || !active.Add(use.Variable)) return null;
                Expr? value = null;
                if (phis.TryGetValue(use.Variable, out var merged) && merged.Block == block)
                    value = new Use(merged.Phi.Sources[incoming], use.Width);
                else if (definitions.TryGetValue(use.Variable, out var defined)
                    && !ExprMap.Walk(defined).Any(p => p is Load or Intrinsic or FrameAddress)) value = defined;
                var expanded = value is null ? null : Expand(value, block, incoming, active);
                active.Remove(use.Variable);
                return expanded is null ? null : expanded.Width == use.Width ? expanded : Fold.Convert(ConvKind.Truncate, expanded, use.Width);
            }));
        }
        // null 表示尚不能判定；空集合表示该来源不可能满足被检查对象为 null。
        ulong[]? UnderNull(Expr expression, Variable checkedValue, HashSet<Variable> active)
        {
            if (nonNull.Contains(checkedValue)) return [];
            if (active.Count >= 32 || !active.Add(checkedValue)) return null;
            ulong[]? result;
            if (definitions.TryGetValue(checkedValue, out var value) && value is Use copy)
                result = UnderNull(expression, copy.Variable, active);
            else if (phis.TryGetValue(checkedValue, out var merged))
            {
                var outcomes = new HashSet<ulong>();
                var complete = true;
                for (var i = 0; i < merged.Phi.Sources.Length; i++)
                {
                    var selected = Expand(expression, merged.Block, i, []);
                    if (UnderNull(selected, merged.Phi.Sources[i], active) is not { } incoming) { complete = false; break; }
                    outcomes.UnionWith(incoming);
                }
                result = complete ? outcomes.ToArray() : null;
            }
            else result = Expand(expression, null, 0, []) is Const constant ? [constant.Value] : null;
            active.Remove(checkedValue);
            return result;
        }
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is not Branch
                { Condition: Compare { Cond: Cond.Eq or Cond.Ne, Left: Use { Width: 64 } value, Right: Const { Value: 0 } } test } first) continue;
            var zero = block.NormalSuccessors.ElementAt(test.Cond == Cond.Eq ? 0 : 1);
            if (zero.Predecessors.Count != 1 || zero.IsLandingPad
                || zero.Statements.LastOrDefault() is not Branch branch || zero.NormalSuccessors.ToArray() is not [var taken, var fallthrough]) continue;
            if (UnderNull(branch.Condition, value.Variable, []) is not [var outcome]) continue;
            zero.Statements[^1] = new Jump(branch.Address, outcome != 0 ? taken.Start : fallthrough.Start);
            MachineFunction.RemoveEdgeAt(zero, outcome != 0 ? 1 : 0);
            return true;
        }
        return false;
    }
}
