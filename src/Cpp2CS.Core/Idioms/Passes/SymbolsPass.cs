using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Idioms;

internal static class SymbolsPass
{
    internal static void Symbols(this IdiomState state, bool rgctx)
    {
        var dominators = Dominators.Compute(state.function);
        var ownDefinition = state.self?.Method;
        while (true)
        {
            var changed = false;
            Expr? Map(Expr e)
            {
                // FieldInfo 表按声明顺序排列，每项包含 name/type/parent/offset/token，共 32 字节。
                if (e is Load { Width: 64, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef fieldOwner }, Right: Const { Value: RuntimeLayout.ClassFields } } } && fieldOwner.Definition.Fields.Count > 0)
                {
                    changed = true;
                    return new Symbol(SymbolKind.Field, new FieldRef(fieldOwner.Definition.Fields[0], fieldOwner));
                }

                if (e is Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Field, Value: FieldRef field }, Right: Const fieldOffset } && field.DeclaringType is DefinitionRef fieldType && fieldOffset.Value % RuntimeLayout.FieldInfoSize == 0 && fieldType.Definition.Fields.ToList().IndexOf(field.Field) + (long)fieldOffset.Value / RuntimeLayout.FieldInfoSize is var fieldIndex && fieldIndex >= 0 && fieldIndex < fieldType.Definition.Fields.Count)
                {
                    changed = true;
                    return new Symbol(SymbolKind.Field, new FieldRef(fieldType.Definition.Fields[(int)fieldIndex], fieldType));
                }

                // RGCTX 已解析为元数据表后，判空只决定运行时的延迟初始化；托管体使用初始化后的表。
                if (e is Compare { Cond: Cond.Eq or Cond.Ne, Left: Symbol { Kind: SymbolKind.Rgctx, Value: RgctxTable guardTable }, Right: Const { Value: 0 } } guard && state.facts.Registrations.Rgctx.TryGetValue((guardTable.Image, guardTable.Token), out var entries) && entries.Length > 0)
                {
                    changed = true;
                    state.foldedRuntimeGuards = true;
                    state.Result.Hit(Template.MethodRgctxGuard);
                    return Expr.C(guard.Cond == Cond.Ne ? 1UL : 0UL, 1);
                }

                // MethodInfo.slot（uint16）：泛型实例与定义相同，取元数据中的槽位
                if (e is Load { Width: 16, Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Method, Value: MethodRef slotted }, Right: Const { Value: RuntimeLayout.MethodSlot } } } && slotted.Method.Slot is >= 0 and < 0xFFFF)
                {
                    state.Result.Hit(Template.MethodSlot);
                    changed = true;
                    return Expr.C((ulong)slotted.Method.Slot, 16);
                }

                if (e is not Load { Width: 64 } load)
                    return null;
                if (load.Address is Const address && state.facts.Usages.At(address.Value) is { } slot)
                {
                    state.Result.ReadSlots.Add(address.Value);
                    state.Result.Hit(Template.MetadataSlot);
                    changed = true;
                    var symbol = new Symbol(SymbolOfPass.SymbolOf(slot.Usage.Kind), slot.Usage.Value);
                    state.symbolSlots.TryAdd(symbol, address.Value);
                    return symbol;
                }

                var (basis, offset) = SplitPass.Split(load.Address);
                var own = basis is Use { Variable: { Version: 0 } v } && v.Storage == state.selfMethodInfo && ownDefinition is not null;
                Symbol? found = (basis, offset) switch
                {
                    (Symbol { Kind: SymbolKind.Class } c, RuntimeLayout.ClassStaticFields) => new Symbol(SymbolKind.StaticFields, c.Value),
                    (Symbol { Kind: SymbolKind.Method, Value: MethodRef m }, RuntimeLayout.MethodKlass) => new Symbol(SymbolKind.Class, m.DeclaringType),
                    (_, RuntimeLayout.MethodKlass) when own => new Symbol(SymbolKind.Class, GenericFormPass.GenericForm(ownDefinition!.Owner)),
                    (Symbol { Kind: SymbolKind.Method, Value: MethodRef m }, RuntimeLayout.MethodRgctxData) when rgctx => new Symbol(SymbolKind.Rgctx, TablePass.Table(m)),
                    (_, RuntimeLayout.MethodRgctxData) when rgctx && own => new Symbol(SymbolKind.Rgctx, new RgctxTable(ownDefinition!.Owner.Assembly, ownDefinition.Token, ownDefinition.ToString(), null, null)),
                    (Symbol { Kind: SymbolKind.Class, Value: DefinitionRef t }, RuntimeLayout.ClassRgctxData) when rgctx => new Symbol(SymbolKind.Rgctx, TablePass.Table(t)),
                    (Symbol { Kind: SymbolKind.Rgctx, Value: RgctxTable table }, var o) when o % 8 == 0 => state.Entry(table, (int)(o / 8)),
                    _ => null,
                };
                if (found is null)
                    return null;
                state.Result.Hit(found.Kind switch
                {
                    SymbolKind.StaticFields => Template.StaticFields,
                    SymbolKind.Rgctx => Template.RgctxData,
                    _ when basis is Symbol { Kind: SymbolKind.Rgctx } => Template.RgctxEntry,
                    _ => Template.MethodClass,
                });
                changed = true;
                return found;
            }

            foreach (var block in state.function.Blocks)
                for (var i = 0; i < block.Statements.Count; i++)
                    block.Statements[i] = ExprMap.MapOperands(block.Statements[i], e => ExprMap.Map(e, Map));
            if (!changed)
                break;
            Propagate.Run(state.function, dominators);
        }
    }
}
