using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class GuardPass
{
    internal static bool Guard(this IdiomState state, Block head, Branch branch, int side, List<Block> chain, Block merge)
    {
        var statements = chain.SelectMany(b => b.Statements).ToList();
        var calls = statements.OfType<Call>().ToList();
        if (calls.Count == 0)
            return false;
        var helpers = calls.Select(c => state.owner.HelperOf(c)?.Kind).ToList();
        var condition = state.defs.Expand(branch.Condition);
        var loads = TopLoadsPass.TopLoads(condition).Distinct().ToList();
        if (loads.Count != 1)
            return false;
        var load = loads[0];
        bool Decides(ulong enter, ulong skip) => DirectionPass.Direction(condition, ReplacePass.Replace(load, enter)) == side && DirectionPass.Direction(condition, ReplacePass.Replace(load, skip)) == 1 - side;
        // s_Il2CppMethodInitialized：读 1 字节守卫，区域内只有 InitMetadata(槽位)、置位写入与纯定义
        if (helpers.All(k => k == HelperKind.InitMetadata))
        {
            if (load is not { Width: 8, Address: Const guard } || !state.owner.guardSections.Any(s => s.Contains(guard.Value)))
                return false;
            var slots = new List<ulong>();
            var sets = 0;
            foreach (var stmt in statements)
            {
                switch (stmt)
                {
                    case Call call when state.defs.Expand(call.Arguments.FirstOrDefault() ?? Expr.C(0, 64)) is Const slot && state.facts.Usages.At(slot.Value) is not null:
                        slots.Add(slot.Value);
                        break;
                    case Store { Target: Const target, Value: Const { Value: 1, Width: 8 } } when target.Value == guard.Value:
                        sets++;
                        break;
                    case Define { Value: Const or Symbol } or Nop or Jump:
                        break;
                    default:
                        return false;
                }
            }

            if (sets == 0 || !Decides(0, 1) || state.Merge(head, chain, merge, null, null) is not { } overrides)
                return false;
            if (state.recording)
                state.Record(Template.MetadataInitGuard, head, state.Start(head), new() { ["merge"] = merge.Start }, new() { ["guard"] = guard.Value, ["slots"] = slots.ToArray(), ["helpers"] = calls.Select(c => ((Const)c.Target).Value).Distinct().ToArray(), });
            CollapsePass.Collapse(head, merge, head, [], overrides, branch.Address);
            state.Remove(chain);
            state.initializedGuards.Add((head, guard.Value));
            state.Result.GuardSlots[guard.Value] = [.. state.Result.GuardSlots.GetValueOrDefault(guard.Value, []).Union(slots).Order()];
            state.Result.MetadataGuardBranches.Add(branch.Address);
            state.Result.InitializedSlots.UnionWith(slots);
            state.Result.Hit(Template.MetadataInitGuard);
            return true;
        }

        if (calls.Count != 1 || calls[0].Arguments.Length == 0)
            return false;
        var helperCall = calls[0];
        var argument = helperCall.Arguments[0];
        var regionDefined = DefinedPass.Defined(chain);
        if (ExprMap.Walk(argument).OfType<Use>().Any(u => regionDefined.Contains(u.Variable)))
            return false;
        var subject = state.defs.Expand(argument);
        Expr Field(int offset) => Fold.Simplify(new Binary(BinOp.Add, subject, Expr.C((ulong)offset, 64), 64));
        var (kind, template, enter, skip, offset, width, returnsArgument) = helpers[0] switch
        {
            HelperKind.ClassInit => (OpKind.RunClassConstructor, Template.ClassConstructorGuard, 0UL, 1UL, RuntimeLayout.ClassCctorFinishedOrNoCctor, 32, false),
            HelperKind.InitializedTypeInfo => (OpKind.InitClass, Template.InitClassGuard, 0UL, 1UL, RuntimeLayout.ClassBitflags1, 8, true),
            HelperKind.InitMethodRgctx => (OpKind.InitMethodRgctx, Template.MethodRgctxGuard, 0UL, 0x1000UL, RuntimeLayout.MethodRgctxData, 64, true),
            _ => default,
        };
        if (width == 0 || load.Address != Field(offset) || !Decides(enter, skip))
            return false;
        if (kind == OpKind.InitClass)
        {
            if (!ClassInitializationFlags.IsBitTest(condition, load))
                return false;
        }
        else if (load.Width != width)
            return false;
        // 区域内除 helper 调用外只允许纯定义：常量、符号、对守卫字段的重新读取（初始化之后的值）
        if (!statements.All(s => s is Nop or Jump || ReferenceEquals(s, helperCall) || s is Define { Value: Const or Symbol } || s is Define d && ClassInitializationFlags.IsReload(state.defs.Expand(d.Value), load)))
            return false;
        var result = returnsArgument && helperCall.Defines.Length > 0 ? helperCall.Defines[0] : null;
        if (result is not null && statements.Any(s => ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == result)))
            return false;
        var reload = new List<Stmt>();
        var reloaded = new Dictionary<Expr, Variable>();
        Variable Reload(Expr value)
        {
            if (reloaded.TryGetValue(value, out var previous))
                return previous;
            var variable = state.Fresh();
            var source = ExprMap.Map(value, e => e == load ? new Load(Fold.Simplify(new Binary(BinOp.Add, argument, Expr.C((ulong)offset, 64), 64)), load.Width) : null);
            reload.Add(new Define(helperCall.Address, variable, source));
            reloaded[value] = variable;
            return variable;
        }

        if (state.Merge(head, chain, merge, result is null ? null : subject, v => state.defs.Expand(new Use(v, 64)) is var value && ClassInitializationFlags.IsReload(value, load) ? Reload(value) : null) is not { } merged)
            return false;
        var op = new Call(helperCall.Address, CallKind.Direct, helperCall.Target)
        {
            Op = new RuntimeOp(kind, subject is Symbol { Kind: SymbolKind.Class } c ? c.Value : null),
            Arguments = [argument],
        };
        var at = state.recording ? state.Start(head, argument) : default;
        if (state.recording && state.Location(subject, head, at) is { } where)
            state.Record(template, head, at, new() { ["merge"] = merge.Start }, new() { ["subject"] = where, ["helper"] = ((Const)helperCall.Target).Value });
        CollapsePass.Collapse(head, merge, head, [op, .. reload], merged, branch.Address);
        state.Remove(chain);
        state.Result.Hit(template);
        return true;
    }
}
