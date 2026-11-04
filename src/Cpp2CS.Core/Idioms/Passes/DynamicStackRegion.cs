using Cpp2CS.Facts;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>按正的 stackslot_size 连续向下分配的区域，各段按 16 字节对齐。</summary>
internal sealed record DynamicStackRegion(FrameAddress Root, IReadOnlyList<Expr> Sizes)
{
    /// <summary>32 位无符号大小按 16 字节向下分配后的地址，不高于初始帧地址。</summary>
    internal static FrameAddress? Ceiling(Expr expression)
    {
        while (expression is Binary { Op: BinOp.Sub, Left: var upper, Right: Binary { Op: BinOp.And,
            Left: Binary { Op: BinOp.Add, Left: Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand.Width: 32 },
                Right: Const { Value: 15 } }, Right: Const { Value: 0x1fffffff0 or 0xfffffffffffffff0 } } })
            expression = upper;
        return expression as FrameAddress;
    }

    public bool Disjoint(DynamicStackRegion other) => Root == other.Root && Sizes.Count != other.Sizes.Count
        && Sizes.Take(Math.Min(Sizes.Count, other.Sizes.Count)).SequenceEqual(other.Sizes.Take(Math.Min(Sizes.Count, other.Sizes.Count)));

    public static DynamicStackRegion? Parse(Expr expression)
    {
        var sizes = new List<Expr>();
        while (expression is Binary { Op: BinOp.Sub, Left: var upper, Right: Binary { Op: BinOp.And,
            Left: Binary { Op: BinOp.Add, Left: var size, Right: Const { Value: 15 } }, Right: Const mask } })
        {
            if (sizes.Count >= 16 || mask.Value is not (0x1fffffff0 or 0xfffffffffffffff0)
                || size is not Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand: Load { Width: 32,
                    Address: Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef }, Right: Const { Value: RuntimeLayout.ClassStackSlotSize } } } }) return null;
            sizes.Insert(0, size);
            expression = upper;
        }
        return expression is FrameAddress root && sizes.Count > 0 ? new(root, sizes) : null;
    }
}
