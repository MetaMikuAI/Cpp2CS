using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class GuardsPass
{
    internal static bool Guards(this IdiomState state)
    {
        var changed = false;
        foreach (var head in state.function.Blocks.ToArray())
        {
            if (state.removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch)
                continue;
            var normal = head.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0] == normal[1])
                continue;
            for (var side = 0; side < 2; side++)
            {
                // 两臂都跳到汇合点时，先越过没有活语句的跳过臂，形成标准的元数据或类初始化守卫。
                var skipped = normal[1 - side];
                if (skipped.Predecessors.Count == 1 && !skipped.IsLandingPad && skipped.Statements.All(s => s is Nop or Jump) && skipped.NormalSuccessors.ToArray() is [var merge] && merge != head && ChainPass.Chain(normal[side], merge) is { Count: > 0 } guarded && guarded.SelectMany(b => b.Statements).OfType<Call>().ToArray() is { Length: > 0 } initializers && (initializers.All(c => state.owner.HelperOf(c)?.Kind == HelperKind.InitMetadata) || initializers is [var initializer] && state.owner.HelperOf(initializer)?.Kind is HelperKind.ClassInit or HelperKind.InitializedTypeInfo))
                {
                    var targets = side == 0 ? new List<(Block, Block)>
                    {
                        (normal[0], head),
                        (merge, skipped)
                    }

                    : [(merge, skipped), (normal[1], head)];
                    var rewritten = new Branch(branch.Address, branch.Condition, targets[0].Item1.Start, targets[1].Item1.Start);
                    if (state.Rewire(head, [], rewritten, targets, [skipped]))
                    {
                        state.Remove([skipped]);
                        changed = true;
                        break;
                    }
                }

                if (ChainPass.Chain(normal[side], normal[1 - side]) is not { Count: > 0 } chain)
                    continue;
                if (!state.Guard(head, branch, side, chain, normal[1 - side]))
                    continue;
                changed = true;
                break;
            }
        }

        return changed;
    }
}
