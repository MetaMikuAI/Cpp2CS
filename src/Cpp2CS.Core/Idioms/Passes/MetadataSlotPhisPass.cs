using Cpp2CS.Facts;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomRewriter;

namespace Cpp2CS.Idioms;

internal static class MetadataSlotPhisPass
{
    internal static bool MetadataSlotPhis(this IdiomState state)
    {
        var changed = false;
        var definitions = new Defs(state.function);
        foreach (var block in state.function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (phi.Sources.Length != block.Predecessors.Count || block.Predecessors.Any(p => !p.NormalSuccessors.Contains(block) || p.Handler == block))
                    continue;
                var choices = phi.Sources.Select(v =>
                {
                    var value = state.SlotValue(definitions.Expand(new Use(v, v.Width)), out var slots);
                    return (Value: value, Slots: slots);
                }).ToArray();
                if (choices.Any(c => c.Value is null) || choices.SelectMany(c => c.Slots).Select(s => SymbolOfPass.SymbolOf(s.Usage.Kind)).Distinct().Count() != 1)
                    continue;
                var loads = state.All.SelectMany(ExprMap.Operands).SelectMany(ExprMap.Walk).OfType<Load>().Where(l => l is { Width: 64, Address: Use use } && use.Variable == phi.Target).ToHashSet();
                var initializers = state.All.OfType<Call>().Where(c => c.Kind == CallKind.Direct && state.owner.HelperOf(c)?.Kind == HelperKind.InitMetadata && c.Arguments is [Use { Variable: var argument }, ..] && argument == phi.Target && c.Defines.Length <= 1).ToHashSet(ReferenceEqualityComparer.Instance);
                if (loads.Count == 0 && initializers.Count == 0)
                    continue;
                var target = state.Fresh();
                var sources = new Variable[choices.Length];
                for (var i = 0; i < choices.Length; i++)
                {
                    var parent = block.Predecessors[i];
                    var last = parent.Statements.LastOrDefault();
                    var position = parent.Statements.Count - (last is Jump or Branch or IndirectJump or Return ? 1 : 0);
                    sources[i] = state.Fresh();
                    parent.Statements.Insert(position, new Define(last?.Address ?? parent.Start, sources[i], choices[i].Value!));
                    foreach (var slot in choices[i].Slots)
                    {
                        state.Result.ReadSlots.Add(slot.Address);
                        if (initializers.Count > 0)
                            state.Result.InitializedSlots.Add(slot.Address);
                        state.symbolSlots.TryAdd(new Symbol(SymbolOfPass.SymbolOf(slot.Usage.Kind), slot.Usage.Value), slot.Address);
                    }
                }

                block.Statements.Insert(block.Statements.IndexOf(phi) + 1, new Phi(phi.Address, target, sources));
                foreach (var member in state.function.Blocks)
                    for (var i = 0; i < member.Statements.Count; i++)
                        if (member.Statements[i] is Call call && initializers.Contains(call))
                        {
                            member.Statements[i] = call.Defines is [var result] ? new Define(call.Address, result, new Use(target, 64)) : new Nop(call.Address, "InitMetadata");
                            state.Result.Hit(Template.LazyMetadataInit);
                        }
                        else
                            member.Statements[i] = ExprMap.MapOperands(member.Statements[i], e => ExprMap.Map(e, part => part is Load load && loads.Contains(load) ? new Use(target, 64) : null));
                state.Result.Hit(Template.MetadataSlot);
                changed = true;
            }

        return changed;
    }
}
