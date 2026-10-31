using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>按调用签名保留有效低位；折叠掩码和副本，不移动内存读取。</summary>
internal static class CallArgumentProjection
{
    internal static Expr Low(Expr expression, int width, IReadOnlyDictionary<Variable, Expr> definitions)
    {
        var active = new HashSet<Variable>();
        var budget = 128;
        Expr Reduce(Expr value)
        {
            var narrowed = Fold.Convert(ConvKind.Truncate, value, width);
            if (--budget < 0) return narrowed;
            if (narrowed is Use use && active.Add(use.Variable))
            {
                var reduced = definitions.TryGetValue(use.Variable, out var definition) ? Reduce(definition) : narrowed;
                active.Remove(use.Variable);
                // 只替换已归约到常量或现有快照的结果，避免展开复杂表达式。
                return reduced is Const or Use ? reduced : narrowed;
            }
            if (narrowed is Binary { Op: BinOp.And or BinOp.Or or BinOp.Xor } binary)
                return Fold.Binary(binary.Op, Reduce(binary.Left), Reduce(binary.Right), width);
            return narrowed;
        }
        return Reduce(expression);
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
