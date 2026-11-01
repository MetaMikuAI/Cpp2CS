using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Idioms;

internal static class TypeChecksPass
{
    internal static bool TypeChecks(this IdiomState state)
    {
        var changed = false;
        var reuseChecks = new List<Action>();
        foreach (var head in state.function.Blocks.ToArray())
        {
            if (state.removed.Contains(head) || head.Statements.LastOrDefault() is not Branch branch)
                continue;
            var normal = head.NormalSuccessors.ToArray();
            if (normal.Length != 2 || normal[0] == normal[1])
                continue;
            // 深度比较：Ult(objDepth, typeDepth) 跳到失败一侧（或 Uge 跳到继续一侧）
            if (StripConversionsPass.StripConversions(Fold.Simplify(branch.Condition)) is not Compare { Cond: Cond.Ult or Cond.Uge } depth)
                continue;
            if (StripConversionsPass.StripConversions(state.RawDefinition(StripConversionsPass.StripConversions(depth.Left)) ?? depth.Left) is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } objectDepth })
                continue;
            var expandedTypeDepth = StripConversionsPass.StripConversions(state.defs.Expand(depth.Right));
            if (expandedTypeDepth is not Load { Width: 8, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class } type, Right: Const { Value: RuntimeLayout.ClassTypeHierarchyDepth } } })
                continue;
            var klass = objectDepth.Left;
            var (fail, next) = depth.Cond == Cond.Ult ? (normal[0], normal[1]) : (normal[1], normal[0]);
            if (next.Predecessors.Count != 1 || next.IsLandingPad)
                continue;
            // 继承链比较：*(klass->typeHierarchy + depth*8 - 8) == T
            var hierarchy = Fold.Simplify(new Load(Fold.Simplify(new Binary(BinOp.Add, state.defs.Expand(klass), Expr.C(RuntimeLayout.ClassTypeHierarchy, 64), 64)), 64));
            bool IsHierarchyTest(Expr e, out bool equal)
            {
                equal = false;
                if (state.defs.Expand(e) is not Compare { Cond: Cond.Eq or Cond.Ne } c)
                    return false;
                var (entry, symbol) = c.Right is Symbol ? (c.Left, c.Right) : (c.Right, c.Left);
                equal = c.Cond == Cond.Eq;
                return symbol == type && entry is Load { Width: 64 } entryLoad && TermsPass.Terms(entryLoad.Address).Contains(hierarchy);
            }

            var result = state.Fresh();
            var op = new Call(branch.Address, CallKind.Direct, Expr.C(0, 64))
            {
                Op = new RuntimeOp(OpKind.TypeCheck, type.Value),
                Arguments = [klass],
                Results = [result.Storage],
                Defines = [result],
            };
            var isType = new Compare(Cond.Ne, new Use(result, 64), Expr.C(0, 64));
            var replaced = false;
            Expr? Substitute(Expr e)
            {
                if (e is not Compare || !IsHierarchyTest(e, out var equal))
                    return null;
                replaced = true;
                return equal ? isType : new Not(isType);
            }
            // 形态一：next 以继承链比较分支到成功/失败 → 两块合成一个分支
            if (next.Statements.LastOrDefault() is Branch compare && IsHierarchyTest(compare.Condition, out var equalTaken) && next.Statements.Take(next.Statements.Count - 1).All(s => s is Define or Nop) && next.NormalSuccessors.ToArray() is [var a0, var a1] && a0 != a1 && (a0 == fail || a1 == fail) && (a0 == fail ? a1 : a0).Predecessors.Count == 1)
            {
                var success = a0 == fail ? a1 : a0;
                if ((compare.Target == success.Start) != equalTaken || success.Predecessors.Count != 1)
                    continue;
                // 定义随成功边迁移，同一继承链条件也改用已恢复的类型检查结果。
                var moved = next.Statements.OfType<Define>().Select(s => ExprMap.MapOperands(s, e => ExprMap.Map(e, Substitute))).ToList();
                var at = state.recording ? state.Start(head) : default;
                if (state.recording && state.Location(state.defs.Expand(klass), head, at) is { } klassAt && state.Location(type, head, at) is { } typeAt)
                    state.Record(Template.InlineTypeCheck, head, at, new() { ["fail"] = fail.Start, ["success"] = success.Start }, new() { ["klass"] = klassAt, ["type"] = typeAt });
                if (!state.Rewire(head, [op], new Branch(branch.Address, new Compare(Cond.Eq, new Use(result, 64), Expr.C(0, 64)), fail.Start, success.Start), [(fail, head), (success, next)], [next]))
                    continue;
                success.Statements.InsertRange(success.Statements.TakeWhile(s => s is Phi).Count(), moved);
                state.Remove([next]);
            }
            // 形态二：next 中以继承链比较作条件（如 as 的 Select）→ 原位替换为 TypeCheck 的结果（next 中深度检查已通过，两者等价）
            else
            {
                for (var i = 0; i < next.Statements.Count; i++)
                    next.Statements[i] = ExprMap.MapOperands(next.Statements[i], e => ExprMap.Map(e, Substitute));
                if (!replaced)
                    continue;
                head.Statements.Insert(head.Statements.Count - 1, op);
                head.Statements[^1] = branch with
                {
                    Condition = depth.Cond == Cond.Ult ? new Not(isType) : isType
                };
            }

            // 同一类继承表不会因字段写入改变；支配区域中的重复比较复用此次检查。
            // 先识别其余完整检查，避免提前改掉它们的继承链条件而留下孤立深度检查。
            reuseChecks.Add(() =>
            {
                var bypassed = new HashSet<Block>();
                var pending = new Stack<Block>();
                pending.Push(state.function.EntryBlock);
                while (pending.TryPop(out var reachable))
                {
                    if (reachable == head || !bypassed.Add(reachable)) continue;
                    foreach (var successor in reachable.Successors) pending.Push(successor);
                }
                foreach (var block in state.function.Blocks.Where(b => b != head && !state.removed.Contains(b) && !bypassed.Contains(b)))
                    for (var i = 0; i < block.Statements.Count; i++)
                        block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Substitute));
            });

            state.Result.Hit(Template.InlineTypeCheck);
            changed = true;
        }

        foreach (var reuse in reuseChecks) reuse();
        return changed;
    }
}
