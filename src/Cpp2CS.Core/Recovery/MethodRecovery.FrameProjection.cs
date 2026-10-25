using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        /// <summary>
        /// W 位 AShr(x,k) 等于对 x[k..W) 作符号扩展。先沿已证明的片投影，再扩展，
        /// 避免把栈帧叶子重新拼成整数后读取最终会被截掉的其他字段。
        /// 仅用于本阶段已建立栈结构体根的方法；原生移位量仍按 W 取模。
        /// </summary>
        private ManagedValue? FrameShift(BinOp operation, ManagedValue left, ManagedValue right, int width)
        {
            if (frameRegions.Count == 0 || operation != BinOp.AShr || right is not ConstantValue shift || width is not (32 or 64)) return null;
            var low = (int)(shift.Bits & (ulong)(width - 1));
            var narrow = width - low;
            if (narrow is not (8 or 16 or 32) || narrow == width) return null;
            var leaf = Slice(left, low, narrow);
            return new ConversionValue(ConvKind.SignExtend, leaf, types.Integer(width, true), width);
        }
    }
}
