using Cpp2CS.Recovery.Analysis;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>
        /// W 位右移先投影 x[k..W)，再按指令作符号或零扩展，
        /// 避免把栈帧叶子重新拼成整数后读取最终会被截掉的其他字段。
        /// 结构体片不要求来自栈帧；原生移位量仍按 W 取模。
        /// </summary>
        private RecoveryResult<ManagedValue?> FrameShift(BinOp operation, ManagedValue left, ManagedValue right, int width)
        {
            if (operation is not (BinOp.AShr or BinOp.LShr) || right is not ConstantValue shift || width is not (32 or 64)
                || left is not Fragment && (frameRegions.Count == 0 || operation != BinOp.AShr)) return (ManagedValue?)null;
            var low = (int)(shift.Bits & (ulong)(width - 1));
            var narrow = width - low;
            if (narrow is not (8 or 16 or 32) || narrow == width) return (ManagedValue?)null;
            if (!Slice(left, low, narrow).TryGet(out var leaf, out var failure)) return failure;
            if (operation == BinOp.LShr)
                return ResizeFragment(new Fragment([new Part(0, leaf)], types.UInt64, narrow), width).Map<ManagedValue?>(value => value);
            if (!Coerce(leaf, types.Integer(narrow, false), 0).TryGet(out leaf, out failure)) return failure;
            return new ConversionValue(ConvKind.SignExtend, leaf, types.Integer(width, true), width);
        }
    }
}
