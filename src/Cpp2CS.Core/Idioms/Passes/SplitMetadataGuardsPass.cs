using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class SplitMetadataGuardsPass
{
    internal static bool SplitMetadataGuards(this IdiomState state)
    {
        var changed = false;
        foreach (var head in state.function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.ToArray() is not [var first, var second])
                continue;
            var condition = state.defs.Expand(branch.Condition);
            if (TopLoadsPass.TopLoads(condition).Distinct().ToArray() is not [Load { Width: 8, Address: Const guard } load] || !state.owner.guardSections.Any(s => s.Contains(guard.Value)))
                continue;
            var side = DirectionPass.Direction(condition, ReplacePass.Replace(load, 0));
            if (side is not (0 or 1) || DirectionPass.Direction(condition, ReplacePass.Replace(load, 1)) != 1 - side)
                continue;
            var init = side == 0 ? first : second;
            var skip = side == 0 ? second : first;
            if (init.IsLandingPad || init.Predecessors.Count != 1 || init.Statements.LastOrDefault() is not Branch after || skip.Statements.LastOrDefault() is not Branch normal || skip.Statements.Any(s => s is not (Define or Nop or Branch)))
                continue;
            var left = state.defs.Expand(after.Condition);
            var right = state.defs.Expand(normal.Condition);
            if (!(left == right && after.Target == normal.Target && after.Fallthrough == normal.Fallthrough) && !(left == Fold.Simplify(new Not(right)) && after.Target == normal.Fallthrough && after.Fallthrough == normal.Target))
                continue;
            var slots = new List<ulong>();
            var sets = 0;
            var valid = true;
            foreach (var statement in init.Statements.SkipLast(1))
                switch (statement)
                {
                    case Call call when state.owner.HelperOf(call)?.Kind == HelperKind.InitMetadata && state.defs.Expand(call.Arguments.FirstOrDefault() ?? Expr.C(0, 64)) is Const slot && state.facts.Usages.At(slot.Value) is not null:
                        slots.Add(slot.Value);
                        break;
                    case Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } when target.Value == guard.Value:
                        sets++;
                        break;
                    case Define { Value: Const or Symbol } or Nop:
                        break;
                    default:
                        valid = false;
                        break;
                }

            if (!valid || slots.Count == 0 || sets != 1)
                continue;
            head.Statements[^1] = new Jump(branch.Address, skip.Start);
            MachineFunction.RemoveEdgeAt(head, side.Value);
            state.initializedGuards.Add((head, guard.Value));
            state.Result.GuardSlots[guard.Value] = slots.Distinct().Order().ToArray();
            state.Result.InitializedSlots.UnionWith(slots);
            state.Result.MetadataGuardBranches.Add(branch.Address);
            state.Result.Hit(Template.MetadataInitGuard);
            changed = true;
        }

        return changed;
    }
}
