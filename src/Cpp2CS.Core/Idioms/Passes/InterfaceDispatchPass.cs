using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class InterfaceDispatchPass
{
    internal static bool InterfaceDispatch(this IdiomState state)
    {
        var dominators = Dominators.Compute(state.function);
        var changed = false;
        foreach (var slow in state.function.Blocks.ToArray())
        {
            if (state.removed.Contains(slow))
                continue;
            var call = slow.Statements.OfType<Call>().FirstOrDefault(c => c.Op is null && state.owner.HelperOf(c)?.Kind == HelperKind.InterfaceLookup);
            if (call is null || call.Arguments.Length < 3 || call.Results.Length == 0 || call.Results[0] != Storage.Gpr(0) || call.Defines.FirstOrDefault() is not { } result)
                continue;
            // 慢路径块处于 try 区间时，调用之后另有一个只含跳转的块
            var slowExit = slow;
            while (slowExit.NormalSuccessors.ToArray() is [var only] && only.Predecessors.Count == 1 && only.Statements.All(s => s is Jump or Nop) && only != slow)
                slowExit = only;
            if (slowExit.NormalSuccessors.ToArray() is not [var merge])
                continue;
            var head = state.function.Blocks[dominators.Idom[merge.Index]];
            if (head == merge || state.removed.Contains(head) || head.Statements.LastOrDefault() is not Branch)
                continue;
            var region = new HashSet<Block>();
            var work = new Stack<Block>(head.NormalSuccessors);
            var valid = true;
            while (work.Count > 0 && valid)
            {
                var b = work.Pop();
                if (b == merge || b == head || !region.Add(b))
                    continue;
                if (!dominators.Dominates(head.Index, b.Index) || region.Count > 32 || b.IsLandingPad)
                    valid = false;
                foreach (var n in b.NormalSuccessors)
                    work.Push(n);
            }

            if (!valid || !region.Contains(slow) || merge.Predecessors.Contains(head))
                continue;
            if (!region.SelectMany(b => b.Statements).All(s => s is Define or Phi or Branch or Jump or Nop || ReferenceEquals(s, call)))
                continue;
            var fromRegion = merge.Predecessors.Where(region.Contains).Distinct().ToArray();
            if (fromRegion.Length != 2 || merge.Predecessors.Count(region.Contains) != 2 || !fromRegion.Contains(slowExit))
                continue;
            var hit = fromRegion.Single(p => p != slowExit);
            int slowIndex = merge.Predecessors.IndexOf(slowExit), hitIndex = merge.Predecessors.IndexOf(hit);
            var phis = merge.Statements.OfType<Phi>().ToList();
            var selected = phis.Where(p => p.Sources[slowIndex] == result).ToList();
            if (selected.Count != 1)
                continue;
            var regionDefined = DefinedPass.Defined(region);
            // 其他 φ 在命中一侧取区域内部的值时：clang 把与查找无关的纯计算下沉进两臂时，两臂的值相同，提到头块定义一次；
            // 否则慢路径一侧必须是未定义值（或该 φ 没有实际使用），合并后改为未定义值
            var overrides = new Dictionary<Variable, Variable>();
            var hoisted = new List<Stmt>();
            var consistent = true;
            foreach (var p in phis.Where(p => p != selected[0] && regionDefined.Contains(p.Sources[hitIndex])))
            {
                if (SameInBothArms(state, p, slowIndex, hitIndex, regionDefined) is { } same)
                {
                    var value = state.Fresh(p.Target.Width);
                    hoisted.Add(new Define(call.Address, value, same));
                    overrides[p.Target] = value;
                    continue;
                }

                if (p.Sources[slowIndex].Version >= 0 && state.Used(p.Target))
                {
                    consistent = false;
                    break;
                }

                overrides[p.Target] = new Variable(p.Target.Storage, -1);
            }

            if (!consistent)
                continue;
            if (call.Arguments.Take(3).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => regionDefined.Contains(u.Variable)))
                continue;
            if (state.defs.Expand(call.Arguments[2]) is not Const slot)
                continue;
            var target = state.defs.Expand(call.Arguments[0]);
            // 命中一侧的值 = klass + (offset << 4) + vtable + slot * 16，klass = *obj
            // 槽位或者加在常量里（vtable + slot*16），或者先加到 offset 上再移位（(offset + slot) << 4）
            var terms = TermsPass.Terms(state.defs.Expand(new Use(selected[0].Sources[hitIndex], 64)));
            var constant = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
            var scaled = terms.Where(t => t is not Const && t != new Load(target, 64)).ToList();
            if (!terms.Contains(new Load(target, 64)) || scaled is not [Binary { Op: BinOp.Shl, Right: Const { Value: 4 } } shifted])
                continue;
            if (constant != (ulong)RuntimeLayout.VtableMethodPointer((int)slot.Value) && !(constant == (ulong)RuntimeLayout.ClassVtable && slot.Value > 0 && ExprMap.Walk(shifted.Left).Contains(Expr.C(slot.Value, 32))))
                continue;
            var iface = state.defs.Expand(call.Arguments[1]);
            var operand = (iface is Symbol { Kind: SymbolKind.Class } c ? c.Value : null, (int)slot.Value);
            var data = state.Fresh();
            var op = new Call(call.Address, CallKind.Direct, call.Target)
            {
                Op = new RuntimeOp(OpKind.InterfaceInvokeData, operand),
                Arguments = [call.Arguments[0], call.Arguments[1], slot],
                Results = [data.Storage],
                Defines = [data],
            };
            var at = state.recording ? state.Start(head, call.Arguments[0], call.Arguments[1]) : default;
            if (state.recording && state.Location(target, head, at) is { } objectAt && state.Location(iface, head, at) is { } ifaceAt && selected[0].Target.Storage.Bank == Bank.Gpr)
                state.Record(Template.InterfaceDispatch, head, at, new() { ["merge"] = merge.Start }, new() { ["object"] = objectAt, ["interface"] = ifaceAt, ["slot"] = slot.Value, ["result"] = $"x{selected[0].Target.Storage.Index}", ["helper"] = ((Const)call.Target).Value, });
            overrides[selected[0].Target] = data;
            CollapsePass.Collapse(head, merge, hit, [.. hoisted, op], overrides, call.Address);
            state.Remove(region);
            state.interfaceData[data] = operand;
            state.Result.Hit(Template.InterfaceDispatch);
            changed = true;
        }

        return changed;
    }

    /// <summary>φ 的两侧展开后是同一个不读内存、只依赖区域之外的值的表达式时返回它；查找本身不改变这样的值，所以与走哪一臂无关。</summary>
    private static Expr? SameInBothArms(IdiomState state, Phi phi, int slowIndex, int hitIndex, HashSet<Variable> regionDefined)
    {
        var value = state.defs.Expand(new Use(phi.Sources[hitIndex], phi.Target.Width));
        if (state.defs.Expand(new Use(phi.Sources[slowIndex], phi.Target.Width)) != value) return null;
        foreach (var part in ExprMap.Walk(value))
            if (part is Load || part is Use use && regionDefined.Contains(use.Variable)) return null;
        return value;
    }
}
