using Cpp2CS.Ir;

namespace Cpp2CS.Extensions.SourceView;

public static partial class AsyncLifting
{
    private sealed partial class Lifter
    {
        // 挂起边消除后，状态号经循环 phi 和异常备份传递；只有全部来源为同一常量才折叠。
        private Dictionary<Variable, ulong> ConstantCopies()
        {
            var statements = blocks.Values.SelectMany(s => s).ToArray();
            var addressed = statements.SelectMany(s => ManagedValues.Of(s).Concat(ManagedValues.CopiedValues(s)))
                .SelectMany(ManagedValues.Walk).OfType<AddressValue>().SelectMany(ManagedValues.Walk)
                .OfType<LocalValue>().Select(l => l.Variable).ToHashSet();
            var definitions = statements.OfType<ManagedAssignment>().Select(a => (a.Target.Variable, a.Value))
                .Concat(statements.SelectMany(ManagedValues.Edges).SelectMany(e => e.Copies).Select(c => (c.Target.Variable, c.Value)))
                .GroupBy(p => p.Variable).ToDictionary(g => g.Key, g => g.Select(p => p.Value).ToArray());
            var unknown = statements.OfType<ManagedCall>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)
                .Concat(statements.OfType<ManagedAwait>().Where(c => c.Result is not null).Select(c => c.Result!.Variable)).Concat(addressed).ToHashSet();
            HashSet<ulong>? Values(ManagedValue value, HashSet<Variable> active)
            {
                if (value is ConstantValue constant) return [constant.Bits & Mask(constant.Width)];
                if (value is FieldValue field && ThisField(field) == State) return [Mask(field.Width)];
                if (value is ConversionValue { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion)
                {
                    var values = Values(conversion.Operand, active);
                    return values?.Select(v => (conversion.Kind == ConvKind.SignExtend ? SignExtend(v, conversion.Operand.Width) : v) & Mask(conversion.Width)).ToHashSet();
                }
                if (value is not LocalValue local || unknown.Contains(local.Variable) || !definitions.TryGetValue(local.Variable, out var sources)) return null;
                if (!active.Add(local.Variable)) return [];
                var result = new HashSet<ulong>();
                foreach (var source in sources)
                {
                    if (Values(source, active) is not { } incoming) { active.Remove(local.Variable); return null; }
                    result.UnionWith(incoming);
                    if (result.Count > 1) break;
                }
                active.Remove(local.Variable);
                return result;
            }
            var known = new Dictionary<Variable, ulong>();
            foreach (var (variable, sources) in definitions)
            {
                var values = new HashSet<ulong>();
                var complete = true;
                foreach (var source in sources)
                {
                    if (Values(source, [variable]) is not { } incoming) { complete = false; break; }
                    values.UnionWith(incoming);
                }
                if (complete && values.Count == 1 && !unknown.Contains(variable)) known[variable] = values.Single();
            }
            return known;
        }
    }
}
