using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

internal static class ArrayCursorsRules
{
    internal static void PrepareArrayCursors(this AnalysisScope ctx)
    {
        if (!ctx.Maintain.Fixpoint("memory.array-cursors", Maintenance.SafetyBudget, () =>
        {
            var changed = false;
            foreach (var cursor in ArrayCursorRecognition.Read(ctx.function, expression => ctx.TypeOfAddressBase(expression) is ArrayRef { IsVector: true } array ? ctx.types.Size(array.Element) : null))
            {
                // 归纳根保留为真实 SSA 值，避免两个等步长游标相互展开。
                if (ExprMap.Walk(cursor.Address).OfType<Use>().Any(u => ctx.State.Arrays.arrayCursors.ContainsKey(u.Variable)))
                    continue;
                if (!ctx.State.Arrays.arrayCursors.TryAdd(cursor.Pointer, cursor.Address))
                    continue;
                ctx.State.Runtime.runtime.Add(cursor.Pointer);
                ctx.State.Runtime.runtime.UnionWith(cursor.AddressCopies);
                if (cursor.IsOffset)
                {
                    ctx.State.Arrays.arrayOffsets[cursor.Pointer] = Fold.Simplify(cursor.Address);
                    foreach (var copy in cursor.AddressCopies)
                        ctx.State.Arrays.arrayOffsets[copy] = ctx.values[copy];
                }

                changed = true;
            }

            foreach (var (variable, expression) in ctx.values)
            {
                if (ctx.State.Arrays.arrayCursors.ContainsKey(variable) || expression is not Binary { Op: BinOp.Add } || ExprMap.Walk(expression).Any(e => e is not (Use or Const or Ir.Binary or Ir.Convert)) || ctx.ArrayLocation(expression) is null)
                    continue;
                // 只展开纯地址计算；数组引用的字段读取仍使用原 SSA 快照。
                ctx.State.Arrays.arrayCursors[variable] = expression;
                ctx.State.Runtime.runtime.Add(variable);
                changed = true;
            }

            if (changed)
                ctx.Maintain.Types("memory.array-cursors.round");
            return changed;
        }))
            ctx.Hole(ctx.entry, $"不动点 数组游标超过 {Maintenance.SafetyBudget} 轮未收敛", rule: "Fixpoint");
    }

    [Step("memory.post-frame-arrays", StepPhase.Analyze, StepKind.Rewrite, Order = 370, After = ["frames.integer-slots"], Name = "帧后数组地址", Refresh = StepRefresh.Types)]
    internal static void PrepareFrameArrayAddresses(this RewriteScope ctx)
    {
        ctx.NormalizePinnedArrays(false);
        ctx.PrepareArrayCursors();
    }
}
