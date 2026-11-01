using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class RetainMetadataPathPass
{
    internal static bool RetainMetadataPath(this IdiomState state)
    {
        var changed = false;
        foreach (var head in state.function.Blocks)
        {
            if (state.removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.ToArray() is not [var first, var second])
                continue;
            var condition = state.defs.Expand(branch.Condition);
            if (TopLoadsPass.TopLoads(condition).Distinct().ToArray() is not [Load { Width: 8, Address: Const guard } load] || !state.owner.guardSections.Any(s => s.Contains(guard.Value)))
                continue;
            var side = DirectionPass.Direction(condition, ReplacePass.Replace(load, 0));
            if (side is not (0 or 1) || DirectionPass.Direction(condition, ReplacePass.Replace(load, 1)) != 1 - side)
                continue;
            var init = side == 0 ? first : second;
            var skip = side == 0 ? second : first;
            if (ChainPass.Chain(init, skip) is not { Count: > 0 } chain)
                continue;
            var statements = chain.SelectMany(b => b.Statements).ToArray();
            var calls = statements.OfType<Call>().ToArray();
            var stores = statements.OfType<Store>().ToArray();
            if (calls.Length == 0 || stores is not [Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } set] || target.Value != guard.Value || calls.Any(c => state.owner.HelperOf(c)?.Kind != HelperKind.InitMetadata) || statements.Any(s => s is not (Call or Store or Define or Nop or Jump)))
                continue;
            var slots = calls.Select(c => state.defs.Expand(c.Arguments.FirstOrDefault() ?? Expr.C(0, 64))).OfType<Const>().Select(c => c.Value).ToArray();
            if (slots.Length != calls.Length || slots.Any(s => state.facts.Usages.At(s) is null))
                continue;
            var storeBlock = chain.Single(b => b.Statements.Contains(set));
            storeBlock.Statements[storeBlock.Statements.IndexOf(set)] = new Nop(set.Address, "MetadataInitGuard");
            state.initializedGuards.Add((storeBlock, guard.Value));
            head.Statements[^1] = new Jump(branch.Address, init.Start);
            MachineFunction.RemoveEdgeAt(head, 1 - side.Value);
            state.Result.GuardSlots[guard.Value] = slots.Distinct().Order().ToArray();
            state.Result.InitializedSlots.UnionWith(slots);
            state.Result.MetadataGuardBranches.Add(branch.Address);
            state.Result.Hit(Template.MetadataInitGuard);
            changed = true;
        }

        return changed;
    }
}
