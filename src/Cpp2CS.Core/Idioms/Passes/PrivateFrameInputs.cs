using Cpp2CS.Ir;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

/// <summary>入口值或不可变元数据经独占栈槽保存与读回的来源证明。</summary>
internal static class PrivateFrameInputs
{
    internal static bool Exposes(Expr expression, FrameAddress sought) => expression is not Load
        && !(DynamicStackRegion.Parse(expression) is { } region && region.Root.Offset <= sought.Offset)
        && (expression is FrameAddress frame ? frame.Offset < sought.Offset + 8 : ExprMap.Children(expression).Any(e => Exposes(e, sought)));

    internal static Expr? Origin(IdiomState state, Expr value, Func<Expr, bool> input)
    {
        Expr Expand(Expr expression) => state.defs.Expand(expression, 24);
        value = Expand(value);
        if (input(value)) return value;
        if (value is not Load { Width: 64, Address: FrameAddress slot }) return null;
        var sites = state.function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Block: b, Index: i, Statement: s))).ToArray();
        var stores = sites.Where(s => s.Statement is Store store && Expand(store.Target) is FrameAddress frame
            && frame.Offset < slot.Offset + 8 && slot.Offset < frame.Offset + store.Value.Width / 8).ToArray();
        if (stores is not [var written] || written.Statement is not Store { Value.Width: 64 } saved
            || Expand(saved.Target) != slot || !input(Expand(saved.Value))) return null;
        var dominators = Dominators.Compute(state.function);
        foreach (var site in sites)
        {
            foreach (var load in ExprMap.Operands(site.Statement).SelectMany(ExprMap.Walk).OfType<Load>())
                if (Expand(load.Address) is FrameAddress frame && frame.Offset < slot.Offset + 8 && slot.Offset < frame.Offset + load.Width / 8
                    && (frame != slot || load.Width != 64 || !dominators.Dominates(written.Block.Index, site.Block.Index)
                        || written.Block == site.Block && written.Index >= site.Index)) return null;
            IEnumerable<Expr> exposed = site.Statement switch
            {
                Define => [],
                Store store when Expand(store.Target) is FrameAddress => [store.Value],
                Call call => call.Arguments,
                Phi phi => phi.Sources.Select(v => (Expr)new Use(v, v.Width)),
                _ => ExprMap.Operands(site.Statement),
            };
            if (exposed.Select(Expand).Any(e => Exposes(e, slot))) return null;
        }
        return Expand(saved.Value);
    }

    internal static bool ForwardMetadata(IdiomState state)
    {
        bool Known(Expr source) => source is Use { Variable.Version: 0 } use && use.Variable.Storage == state.selfMethodInfo
            || source is Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand: Load { Width: 32,
                Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class }, Right: Const { Value: RuntimeLayout.ClassStackSlotSize } } } };
        var values = new Dictionary<Load, Expr?>();
        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
                block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, value =>
                {
                    if (value is not Load { Width: 64 } load || state.defs.Expand(load.Address, 24) is not FrameAddress) return null;
                    if (!values.TryGetValue(load, out var original))
                        values[load] = original = Origin(state, load, Known);
                    if (original is null) return null;
                    changed = true;
                    return original;
                }));
        return changed;
    }
}
