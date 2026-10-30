using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class SharedFieldsRules
{
    internal static Intrinsic FieldAddress(Expr receiver, Symbol field) => new("managed_field_address", [receiver, field], 64);
    internal static TypeRef FieldType(FieldRef field) => field.Field.Type.Substitute(((DefinitionRef)field.DeclaringType).Arguments, []);
    [MachinePass("字段地址", 89, After = ["帧槽", "检查吸收"])]
    internal static void PrepareFieldAddresses(this RecoveryScope ctx)
    {
        ctx.InferTypes();
        var dominators = ctx.Dominators;
        Expr Alias(Expr value, int depth = 32) => depth > 0 && value is Use use && ctx.values.GetValueOrDefault(use.Variable) is Use source ? Alias(source, depth - 1) : value;
        bool Dereferenced(Stmt statement, Expr receiver) => statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var checkedValue] } && Alias(checkedValue) == receiver || ExprMap.Operands(statement).SelectMany(ExprMap.Walk).OfType<Load>().Any(load => ctx.Split(load.Address) is var (root, offset, terms) && root is not null && Alias(root) == receiver && terms.Count == 0 && ctx.types.InstanceField(ctx.TypeOfValue(receiver)!, (int)offset, load.Width / 8) is not null);
        var changed = false;
        foreach (var block in ctx.blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Define definition || definition.Value is not Binary { Op: BinOp.Add, Width: 64 })
                    continue;
                var (root, offset, terms) = ctx.Split(definition.Value);
                if (root is null || terms.Count != 0 || offset < RuntimeLayout.ObjectHeaderSize || offset > int.MaxValue)
                    continue;
                var receiver = Alias(root);
                if (ctx.TypeOfValue(receiver) is not DefinitionRef type || !ManagedTypes.IsReferenceType(type) || ctx.facts.Layouts.Of(type)?.Fields.FirstOrDefault(f => f.Offset == offset) is not { } field)
                    continue;
                if (!ctx.blocks.Where(b => dominators.Dominates(b.Index, block.Index)).Any(b => b.Statements.Take(b == block ? i : b.Statements.Count).Any(s => Dereferenced(s, receiver))))
                    continue;
                var replacement = definition with
                {
                    Value = SharedFieldsRules.FieldAddress(receiver, new Symbol(SymbolKind.Field, new FieldRef(field.Field, type)))
                };
                ctx.Rewriter.Replace(block, i, replacement);
                changed = true;
            }

        if (changed)
            ctx.definitions = ctx.IndexDefinitions();
    }

    internal static void NormalizeSharedFields(this RecoveryScope ctx)
    {
        foreach (var block in ctx.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call)
                    continue;
                if (call.Op is { Kind: OpKind.CallMethodPointer, Operand: MethodRef })
                {
                    ctx.Rewriter.Replace(block, i, call with
                    {
                        Target = Expr.C(0, 64)
                    });
                    continue;
                }

                if (call is { Op.Kind: OpKind.FieldAddress, Arguments: [var receiver, Symbol { Kind: SymbolKind.Field } field] } && call.Defines.FirstOrDefault() is { } result)
                {
                    ctx.Rewriter.Replace(block, i, new Define(call.Address, result, SharedFieldsRules.FieldAddress(receiver, field)));
                    ctx.State.Calls.sharedSites.Add(call.Address);
                }
                else if (call is { Op: null, Target: Const target, Arguments: [var obj, Symbol { Kind: SymbolKind.Field, Value: FieldRef info } symbol, var value, ..] } && ctx.owner.NativeMethods.SharedFieldSetter(target.Value) is > 0 and var width && ctx.types.Bits(SharedFieldsRules.FieldType(info)) == width)
                {
                    ctx.Rewriter.Replace(block, i, new Store(call.Address, SharedFieldsRules.FieldAddress(obj, symbol), value.Width == width ? value : new Ir.Convert(ConvKind.Truncate, value, width)));
                    if (call.Kind == CallKind.Tail)
                        ctx.Rewriter.Insert(block, ++i, new Return(call.Address));
                    ctx.State.Calls.sharedSites.Add(call.Address);
                }
            }
    }

    internal static RecoveryResult<ManagedValue> SharedAddress(this RecoveryScope ctx, Intrinsic address) => address switch
    {
        { Name: "managed_generic_buffer", Arguments: [_, Const id] } => new AddressValue(ctx.State.Frames.sharedBuffers[id.Value]),
        { Name: "managed_generic_argument", Arguments: [_, Const register] } => new AddressValue(ctx.State.Signature.sharedIncoming[Storage.Gpr((int)register.Value)]),
        { Name: "managed_field_address", Arguments: [var receiver, Symbol { Value: FieldRef field }] } => ctx.RecoverAs(receiver, field.DeclaringType, 0).Map<ManagedValue>(value => new AddressValue(new FieldValue(value, field, SharedFieldsRules.FieldType(field), Math.Max(0, ctx.types.Bits(SharedFieldsRules.FieldType(field)))))),
        _ => RecoveryDiagnostics.Fail(0, $"共享地址 {address.Name} 尚未支持", rule: "SharedAddress"),
    };
}
