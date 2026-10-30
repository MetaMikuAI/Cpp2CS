using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class DiscardUnusedInputsPass
{
    internal static void DiscardUnusedInputs(this IdiomState state)
    {
        var phis = state.All.OfType<Phi>().ToDictionary(p => p.Target);
        var metadataResults = state.All.OfType<Call>().Where(c => state.owner.HelperOf(c)?.Kind == HelperKind.InitMetadata).SelectMany(c => c.Defines).ToHashSet();
        bool ResidualInput(Expr value, HashSet<Variable> seen)
        {
            if (value is Unknown or Use { Variable.Version: < 0 } or Symbol { Kind: not SymbolKind.String })
                return true;
            if (value is Ir.Convert convert)
                return ResidualInput(convert.Operand, seen);
            if (value is not Use use || !seen.Add(use.Variable))
                return false;
            if (metadataResults.Contains(use.Variable))
                return true;
            if (state.defs.Raw(use.Variable) is { } source)
                return ResidualInput(source, seen);
            return phis.TryGetValue(use.Variable, out var phi) && phi.Sources.Any(v => ResidualInput(new Use(v, v.Width), seen));
        }

        var changed = false;
        foreach (var block in state.function.Blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call { Op: null, Kind: CallKind.Direct or CallKind.Tail, Target: Const target } call || state.owner.calls.Signature(target.Value) is not { } signature)
                    continue;
                var methods = state.facts.EntriesAt(target.Value).Select(e => e.Method).OfType<MethodRef>().ToArray();
                if (methods.Length == 0 || methods.Any(m => m.Method.Address != target.Value && m.Method.Address != 0 || m.TypeArguments.Concat(m.MethodArguments).Any(FieldLayouts.IsFullyShared)))
                    continue;
                var args = (Expr[])call.Arguments.Clone();
                for (var k = 0; k < args.Length && k < call.Sources.Length; k++)
                {
                    // 原生函数可不读 MethodInfo，但恢复泛型调用仍依赖它选择实例。
                    if (call.Sources[k] == signature.MethodInfo && methods.Any(m => m.Method.GenericParameters.Count != 0 || m.Method.Owner.GenericParameters.Count != 0))
                        continue;
                    if (args[k] is Unknown || !ResidualInput(args[k], []))
                        continue;
                    if (call.Sources[k] != signature.MethodInfo && !state.owner.UnusedInput(target.Value, call.Sources[k]))
                        continue;
                    args[k] = new Unknown("原生被调方未用的输入", args[k].Width);
                    changed = true;
                }

                block.Statements[i] = call with
                {
                    Arguments = args
                };
            }

        if (changed)
            state.Cleanup();
    }
}
