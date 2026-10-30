using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

/// <summary>C# catch 入口的异常对象非空；只沿没有其他写入或取址的引用副本传播。</summary>
internal static class SourceCaughtExceptions
{
    internal static ManagedBody Rewrite(ManagedBody body, ManagedTypes? types = null)
    {
        var statements = body.Blocks.SelectMany(b => b.Statements).ToArray();
        var copies = statements.OfType<ManagedAssignment>().Select(a => new ManagedCopy(a.Target, a.Value))
            .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies)).ToArray();
        var definitions = copies.GroupBy(c => c.Target.Variable).ToDictionary(g => g.Key, g => g.ToArray());
        var unknown = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
            .SelectMany(ManagedValues.Walk).OfType<AddressValue>().Select(a => a.Target).OfType<LocalValue>()
            .Select(l => l.Variable).Concat(statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable))
            .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)).ToHashSet();
        var nonnull = body.Regions.Where(r => r.Kind == ManagedRegionKind.Catch && r.Exception is not null).Select(r => r.Exception!.Variable)
            .Where(v => !definitions.ContainsKey(v) && !unknown.Contains(v)).ToHashSet();
        var caughtTypes = types is null ? new Dictionary<Variable, TypeRef>() : body.Regions
            .Where(r => r.Kind == ManagedRegionKind.Catch && r.Exception is not null && nonnull.Contains(r.Exception.Variable))
            .GroupBy(r => r.Exception!.Variable).Where(g => g.Select(r => r.CatchType ?? types.Corlib("System.Exception")).Distinct().Count() == 1)
            .ToDictionary(g => g.Key, g => g.First().CatchType ?? types.Corlib("System.Exception"));
        bool changed;
        do
        {
            changed = false;
            foreach (var (variable, incoming) in definitions)
                if (!nonnull.Contains(variable) && !unknown.Contains(variable)
                    && incoming.All(c => ManagedTypes.IsReferenceType(c.Target.Type) && c.Value is LocalValue source && nonnull.Contains(source.Variable)))
                {
                    changed |= nonnull.Add(variable);
                    var sources = incoming.Select(c => caughtTypes.GetValueOrDefault(((LocalValue)c.Value).Variable)).Distinct().ToArray();
                    if (sources is [TypeRef type]) caughtTypes[variable] = type;
                }
        } while (changed);
        ManagedValue Simplify(ManagedValue value)
        {
            value = ManagedValues.Map(value, Simplify);
            if (value is IsInstValue { BoxedType: null, Operand: LocalValue source } test && types is not null
                && caughtTypes.TryGetValue(source.Variable, out var type) && types.IsAssignable(type, test.Target)) return source;
            if (value is ComparisonValue { Condition: Cond.Eq or Cond.Ne } condition
                && (Proven(condition.Left, condition.Right) || Proven(condition.Right, condition.Left)))
                return new ConstantValue(condition.Condition == Cond.Ne ? 1UL : 0UL, condition.Type, condition.Width);
            return value;
        }
        bool Proven(ManagedValue value, ManagedValue zero) => value is LocalValue local && nonnull.Contains(local.Variable)
            && zero is ConstantValue { Bits: 0 };
        return body with
        {
            Blocks = body.Blocks.Select(block => block with
            {
                Statements = block.Statements.Select(statement =>
                {
                    statement = ManagedValues.Map(statement, Simplify, target => ManagedValues.Map(target, Simplify));
                    return statement is ManagedBranch { Condition: ConstantValue constant } branch
                        ? new ManagedJump(branch.Address, constant.Bits != 0 ? branch.Taken : branch.Fallthrough) : statement;
                }).ToArray(),
            }).ToArray()
        };
    }
}
