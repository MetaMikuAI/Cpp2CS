using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

/// <summary>引用类型实例字段的地址：在支配位置已解引用接收者时，把“接收者 + 字段偏移”改写为字段地址。</summary>
internal static class FieldAddressesRules
{
    [Step("memory.field-addresses", StepPhase.Analyze, StepKind.Rewrite, Order = 890, After = ["frames.slots", "control.absorb-checks"], Name = "字段地址")]
    internal static void PrepareFieldAddresses(this RecoveryScope ctx)
    {
        ctx.Maintain.Types("memory.field-addresses.entry");
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
            ctx.Maintain.Definitions("memory.field-addresses");
    }
}
