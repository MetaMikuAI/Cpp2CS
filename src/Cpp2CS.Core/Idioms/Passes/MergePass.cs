using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

internal static class MergePass
{
    internal static Dictionary<Variable, Variable>? Merge(this IdiomState state, Block head, List<Block> chain, Block merge, Expr? resultEquals, Func<Variable, Variable?>? reload)
    {
        var regionIndex = merge.Predecessors.IndexOf(chain[^1]);
        var headIndex = merge.Predecessors.IndexOf(head);
        var regionDefined = DefinedPass.Defined(chain);
        var overrides = new Dictionary<Variable, Variable>();
        foreach (var phi in merge.Statements.OfType<Phi>())
        {
            Variable inside = phi.Sources[regionIndex], skipped = phi.Sources[headIndex];
            if (inside == skipped || !regionDefined.Contains(inside))
                continue;
            var call = chain.SelectMany(b => b.Statements).OfType<Call>().FirstOrDefault(c => c.Defines.Contains(inside));
            if (call is not null && resultEquals is not null && call.Defines[0] == inside)
            {
                if (state.defs.Expand(new Use(skipped, 64)) != resultEquals)
                {
                    if (state.Used(phi.Target))
                        return null;
                    overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
                }

                continue;
            }

            if (call is null && reload?.Invoke(inside) is { } fresh)
            {
                overrides[phi.Target] = fresh;
                continue;
            }

            if (call is null && Low(state.defs.Expand(new Use(inside, 64))) == Low(state.defs.Expand(new Use(skipped, 64))))
                continue;
            if (state.Used(phi.Target))
                return null;
            overrides[phi.Target] = new Variable(phi.Target.Storage, -1);
        }

        return overrides;
    }

    /// <summary>
    /// 截断后再扩展回原宽度的值按被截断的值比较。守卫区域按低位保存恢复寄存器时，合并点一侧是 x、另一侧是 x 低位的扩展：
    /// 编译器只保存低位，说明合并后的值只用到低位（否则两条路径上的高位不同），两侧在用到的位上相同。
    /// </summary>
    private static Expr Low(Expr value) => value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend } extended
        && Truncated(extended.Operand) is { } source && source.Width == extended.Width ? Low(source) : value;

    /// <summary>取低位的几种写法：位段、截断、窄读变量或寄存器。返回被截取的整值。</summary>
    private static Expr? Truncated(Expr value) => value switch
    {
        Extract { Low: 0 } extract => extract.Operand,
        Ir.Convert { Kind: ConvKind.Truncate } truncate => truncate.Operand,
        Use use when use.Width < use.Variable.Width => use with { Width = use.Variable.Width },
        Read read when read.Width < read.Storage.Width => read with { Width = read.Storage.Width },
        _ => null,
    };
}
