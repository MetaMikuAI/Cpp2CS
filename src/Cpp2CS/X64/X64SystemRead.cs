using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        // 当前 Profile 不提供 AVX-512 或 AVX10；仅对已核对的形式记录异常边界。
        internal LiftResult DisabledAvx512() => LiftResult.Supported(b.Finish(MirExit.Trap(ExceptionKind.X64InvalidOpcode, "x64.#UD", instruction.IP)));

        private LiftResult ReadSegment()
        {
            if (instruction.OpCount != 2 || !IsScalar(0, false) ||
                Width(0) is not (16 or 32 or 64) || instruction.Op0Kind == OpKind.Memory && Width(0) != 16)
                return Unsupported("段选择子读取需要通用寄存器或 16 位内存目的");
            var selector = b.Read(instruction.Op1Register.ToString().ToLowerInvariant(), 16);
            WriteOperand(0, Resize(selector, Width(0)));
            return Next();
        }
    }
}
