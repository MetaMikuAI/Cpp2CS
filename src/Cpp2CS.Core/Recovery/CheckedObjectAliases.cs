using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>对象已判空、继承检查结果仅用于判空时，保留检查点并为其后的字段和调用恢复派生类型。</summary>
internal static class CheckedObjectAliases
{
    internal static Dictionary<Stmt, Stmt> Read(MachineFunction function, Func<Call, Use?> checkedObject)
    {
        var changes = new Dictionary<Stmt, Stmt>(ReferenceEqualityComparer.Instance);
        if (function.Range.ExceptionRegions.Length != 0) return changes;
        var sites = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i)))
            .ToDictionary(p => p.Statement, p => (p.Block, p.Index), (IEqualityComparer<Stmt>)ReferenceEqualityComparer.Instance);
        var dominators = Dominators.Compute(function);
        bool Before(Stmt first, Stmt next) => sites[first].Block == sites[next].Block ? sites[first].Index < sites[next].Index
            : dominators.Dominates(sites[first].Block.Index, sites[next].Block.Index);
        foreach (var call in function.Blocks.SelectMany(b => b.Statements).OfType<Call>())
        {
            if (call is not { Op: { Kind: OpKind.TypeCheck, Operand: TypeRef target }, Defines: [var flag] }
                || checkedObject(call) is not { } original) continue;
            var users = sites.Keys.Where(s => s is Phi phi && phi.Sources.Contains(flag)
                || ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => u.Variable == flag)).ToArray();
            if (users.Length == 0 || users.Any(s => s is not Call { Op.Kind: OpKind.NullCheck, Arguments: [Use u] } || u.Variable != flag)) continue;
            if (!sites.Keys.OfType<Call>().Any(c => c is { Op.Kind: OpKind.NullCheck, Arguments: [var value] }
                && value == original && Before(c, call))) continue;
            changes[call] = call with { Op = new(OpKind.IsInst, target), Arguments = [original] };
            foreach (var statement in sites.Keys.Where(s => users.Any(g => Before(g, s))))
            {
                var source = changes.GetValueOrDefault(statement) ?? statement;
                var mapped = ExprMap.MapOperands(source, e => ExprMap.Map(e, part => part == original ? new Use(flag, 64) : null));
                if (!ReferenceEquals(source, mapped)) changes[statement] = mapped;
            }
        }
        return changes;
    }
}
