using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>按调用签名保留有效低位；只折叠常量和副本，不移动内存读取。</summary>
internal static class CallArgumentProjection
{
    internal static Expr Low(Expr expression, int width, IReadOnlyDictionary<Variable, Expr> definitions)
    {
        var original = Fold.Convert(ConvKind.Truncate, expression, width);
        var current = original;
        var seen = new HashSet<Variable>();
        while (current is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value))
        {
            var narrowed = Fold.Convert(ConvKind.Truncate, value, width);
            if (narrowed is Const) return narrowed;
            if (narrowed is not Use) break;
            current = narrowed;
        }
        return current;
    }

    public static void Run(IReadOnlyList<Block> blocks, Func<Call, IReadOnlyDictionary<Storage, int>> widths)
    {
        var definitions = blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        foreach (var block in blocks)
            for (var i = 0; i < block.Statements.Count; i++)
            {
                if (block.Statements[i] is not Call call || widths(call) is not { Count: > 0 } parameters) continue;
                var arguments = call.Arguments.Select((e, k) => k < call.Sources.Length && parameters.TryGetValue(call.Sources[k], out var width)
                    && width < e.Width ? Low(e, width, definitions) : e).ToArray();
                if (!arguments.AsSpan().SequenceEqual(call.Arguments)) block.Statements[i] = call with { Arguments = arguments };
            }
    }
}
