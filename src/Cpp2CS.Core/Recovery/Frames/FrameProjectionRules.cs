using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

internal static class FrameProjectionRules
{
    internal static RecoveryResult<ManagedValue?> FrameShift(this RecoveryScope ctx, BinOp operation, ManagedValue left, ManagedValue right, int width)
    {
        if (operation is not (BinOp.AShr or BinOp.LShr) || right is not ConstantValue shift || width is not (32 or 64) || left is not Fragment && (ctx.State.Frames.frameRegions.Count == 0 || operation != BinOp.AShr))
            return (ManagedValue?)null;
        var low = (int)(shift.Bits & (ulong)(width - 1));
        var narrow = width - low;
        if (narrow == width || (operation == BinOp.LShr && left is Fragment ? narrow % 8 != 0 : narrow is not (8 or 16 or 32)))
            return (ManagedValue?)null;
        if (!ctx.Slice(left, low, narrow).TryGet(out var leaf, out var failure))
            return failure;
        if (operation == BinOp.LShr)
            return ctx.ResizeFragment(leaf as Fragment ?? new Fragment([new Part(0, leaf)], ctx.types.UInt64, narrow), width).Map<ManagedValue?>(value => value);
        if (!ctx.Coerce(leaf, ctx.types.Integer(narrow, false), 0).TryGet(out leaf, out failure))
            return failure;
        return new ConversionValue(ConvKind.SignExtend, leaf, ctx.types.Integer(width, true), width);
    }
}
