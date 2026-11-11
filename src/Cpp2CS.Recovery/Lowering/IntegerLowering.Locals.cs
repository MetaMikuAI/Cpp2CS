using Cpp2CS.Managed;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    /// <summary>块内共享的全定义纯表达式只求值一次；除法及含除法的选择留在原求值位置。</summary>
    private ManagedBody Materialize(ManagedBody body)
    {
        var blocks = new List<ManagedBlock>();
        foreach (var block in body.Blocks)
        {
            var counts = new Dictionary<ManagedValue, int>(ReferenceEqualityComparer.Instance);
            var total = new Dictionary<ManagedValue, bool>(ReferenceEqualityComparer.Instance);
            void Count(ManagedValue v)
            {
                if (counts.TryGetValue(v, out var n)) { counts[v] = n + 1; return; }
                counts.Add(v, 1);
                foreach (var child in ManagedValues.Children(v)) Count(child);
            }
            bool Total(ManagedValue v)
            {
                if (total.TryGetValue(v, out var result)) return result;
                result = v is not BinaryValue { Op: BinaryOperator.SignedDivide or BinaryOperator.UnsignedDivide
                    or BinaryOperator.SignedRemainder or BinaryOperator.UnsignedRemainder }
                    && ManagedValues.Children(v).All(Total);
                total.Add(v, result); return result;
            }
            foreach (var s in block.Statements)
                foreach (var v in ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s))) Count(v);
            var locals = new Dictionary<ManagedValue, ManagedValue>(ReferenceEqualityComparer.Instance);
            var statements = new List<ManagedStatement>();
            ManagedValue Rewrite(ManagedValue v)
            {
                if (locals.TryGetValue(v, out var known)) return known;
                var rebuilt = ManagedValues.Map(v, Rewrite);
                if (counts[v] > 1 && v is not (ArgumentValue or LocalValue or ConstantValue) && Total(v))
                {
                    var local = new LocalValue(new(nextLocal++), v.Type, v.Width);
                    statements.Add(new ManagedAssignment(block.Address, local, rebuilt)); rebuilt = local;
                }
                locals.Add(v, rebuilt); return rebuilt;
            }
            foreach (var statement in block.Statements) statements.Add(ManagedValues.Map(statement, Rewrite));
            blocks.Add(block with { Statements = statements });
        }
        return body with { Blocks = blocks };
    }
}
