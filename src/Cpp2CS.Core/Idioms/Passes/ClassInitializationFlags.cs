using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>类初始化低位检查与零扩展重读；其他位仍属于原生布局。</summary>
internal static class ClassInitializationFlags
{
    internal static bool IsBitTest(Expr condition, Load load)
    {
        if (load.Width is not (8 or 16) || condition is not Compare
            {
                Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 },
                Left: Binary { Op: BinOp.And } mask
            }) return false;
        Expr Low(Expr value) => value switch
        {
            Ir.Convert c => Low(c.Operand),
            Extract { Low: 0 } e => Low(e.Operand),
            _ => value,
        };
        // 2022 之前用 initialized 位（0x2），之后用 initialized_and_no_error 位（0x1）。
        return mask.Right is Const { Value: 1 or 2 } && Low(mask.Left) == load
            || mask.Left is Const { Value: 1 or 2 } && Low(mask.Right) == load;
    }

    internal static bool IsReload(Expr value, Load load) => value == load
        || value is Ir.Convert { Kind: ConvKind.ZeroExtend } c && IsReload(c.Operand, load);
}
