using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class ChecksPass
{
    internal static bool Checks(this IdiomState state)
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
                if (state.ThrowBlock(normal[side]) is not { } helper || state.ThrowBlock(normal[1 - side]) is not null)
                    continue;
                if (!FoldedCheckEdges.Preserve(state.function, head, normal[side], side, state.Fresh))
                    continue;
                var condition = Fold.Simplify(side == 0 ? branch.Condition : new Not(branch.Condition));
                var (kind, template, arguments) = (helper.Detail, condition) switch
                {
                    ("System.NullReferenceException", Compare { Cond: Cond.Eq, Left: { Width: 64 } value, Right: Const { Value: 0 } }) => (OpKind.NullCheck, Template.NullCheck, new[] { value }),
                    ("System.IndexOutOfRangeException", Compare { Cond: Cond.Uge or Cond.Ugt or Cond.Ule or Cond.Ult } compare) => (OpKind.BoundsCheck, Template.BoundsCheck, BoundsPass.Bounds(compare)),
                    _ => (OpKind.ThrowIf, Template.ThrowIf, new[] { condition }),
                };
                var op = new Call(branch.Address, CallKind.Direct, ((Call)normal[side].Statements[^1]).Target)
                {
                    Op = new RuntimeOp(kind, kind == OpKind.ThrowIf ? helper.Detail : null),
                    Arguments = arguments,
                    NativeExceptionSite = normal[side].Statements[^1].Address,
                };
                var at = state.recording ? state.Start(head) : default;
                var throwHelper = ((Const)((Call)normal[side].Statements[^1]).Target).Value;
                var exits = new Dictionary<string, ulong>
                {
                    ["throw"] = normal[side].Start,
                    ["pass"] = normal[1 - side].Start
                };
                if (state.recording && kind == OpKind.NullCheck && state.Placement(state.defs.Expand(arguments[0]), head, at) is { } where)
                    state.Record(template, head, at, exits, new() { ["value"] = where, ["helper"] = throwHelper });
                // 越界：idx ≥u len 时抛出（比较宽度为 width）
                if (state.recording && kind == OpKind.BoundsCheck && arguments.Length == 2 && state.Placement(state.defs.Expand(arguments[0]), head, at) is { } indexAt && state.Placement(state.defs.Expand(arguments[1]), head, at) is { } lengthAt)
                    state.Record(template, head, at, exits, new() { ["index"] = indexAt, ["length"] = lengthAt, ["width"] = arguments[0].Width, ["helper"] = throwHelper });
                head.Statements[^1] = op;
                head.Statements.Add(new Jump(branch.Address, normal[1 - side].Start));
                MachineFunction.RemoveEdgeAt(head, side);
                state.Result.Hit(template);
                changed = true;
                break;
            }
        }

        return changed;
    }
}
