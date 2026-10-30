using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class SplitClassGuardsPass
{
    internal static bool SplitClassGuards(this IdiomState state)
    {
        var changed = false;
        foreach (var head in state.function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch guard || head.NormalSuccessors.ToArray() is not [var first, var second])
                continue;
            var condition = state.defs.Expand(guard.Condition);
            if (TopLoadsPass.TopLoads(condition).Distinct().ToArray() is not [Load { Width: 32, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type }, Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor } } } load])
                continue;
            var side = DirectionPass.Direction(condition, ReplacePass.Replace(load, 0));
            if (side is not (0 or 1) || DirectionPass.Direction(condition, ReplacePass.Replace(load, 1)) != 1 - side)
                continue;
            var init = side == 0 ? first : second;
            var skip = side == 0 ? second : first;
            if (init.Predecessors.Count != 1 || init.Handler != head.Handler || skip.Handler != head.Handler || init.IsLandingPad || skip.IsLandingPad || init.Statements.LastOrDefault() is not Branch after || skip.Statements.LastOrDefault() is not Branch normal || skip.Statements.Any(s => s is not (Define or Nop or Branch)))
                continue;
            var prefix = init.Statements.SkipLast(1).Where(s => s is not Nop).ToArray();
            if (prefix is not [Call { Op.Kind: OpKind.RunClassConstructor } call] || !Equals(call.Op.Operand, type))
                continue;
            var a = state.defs.Expand(after.Condition);
            var b = state.defs.Expand(normal.Condition);
            if (!(a == b && ClassGuardExits.Same(init, after.Target, skip, normal.Target) && ClassGuardExits.Same(init, after.Fallthrough, skip, normal.Fallthrough)) && !(a == Fold.Simplify(new Not(b)) && ClassGuardExits.Same(init, after.Target, skip, normal.Fallthrough) && ClassGuardExits.Same(init, after.Fallthrough, skip, normal.Target)))
                continue;
            // RunClassConstructor 自身处理已初始化状态；保留初始化臂及其后续业务分支。
            head.Statements[^1] = new Jump(guard.Address, init.Start);
            MachineFunction.RemoveEdgeAt(head, 1 - side.Value);
            changed = true;
        }

        return changed;
    }
}
