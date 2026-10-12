using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private LiftResult PackedInteger()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1)) return Unsupported("packed 整数运算仅支持 SSE2 XMM 形式");
            SimdAlignment();
            int width = instruction.Mnemonic switch
            {
                Mnemonic.Paddb or Mnemonic.Psubb or Mnemonic.Paddsb or Mnemonic.Paddusb or Mnemonic.Psubsb or Mnemonic.Psubusb
                    or Mnemonic.Pcmpeqb or Mnemonic.Pcmpgtb or Mnemonic.Pminub or Mnemonic.Pmaxub => 8,
                Mnemonic.Paddd or Mnemonic.Psubd or Mnemonic.Pcmpeqd or Mnemonic.Pcmpgtd => 32,
                Mnemonic.Paddq or Mnemonic.Psubq => 64,
                _ => 16
            };
            bool subtract = instruction.Mnemonic is Mnemonic.Psubb or Mnemonic.Psubw or Mnemonic.Psubd or Mnemonic.Psubq
                or Mnemonic.Psubsb or Mnemonic.Psubsw or Mnemonic.Psubusb or Mnemonic.Psubusw;
            bool saturate = instruction.Mnemonic is Mnemonic.Paddsb or Mnemonic.Paddsw or Mnemonic.Paddusb or Mnemonic.Paddusw
                or Mnemonic.Psubsb or Mnemonic.Psubsw or Mnemonic.Psubusb or Mnemonic.Psubusw;
            bool unsigned = instruction.Mnemonic is Mnemonic.Paddusb or Mnemonic.Paddusw or Mnemonic.Psubusb or Mnemonic.Psubusw;
            Value left = ReadXmm(0), right = ReadSimdSource(1, 128);
            List<Value> lanes = [];
            for (int offset = 0; offset < 128; offset += width)
            {
                Value a = b.Extract(left, offset, width), c = b.Extract(right, offset, width), value;
                if (instruction.Mnemonic is Mnemonic.Pcmpeqb or Mnemonic.Pcmpeqw or Mnemonic.Pcmpeqd)
                    value = b.Sext(b.Eq(a, c), width);
                else if (instruction.Mnemonic is Mnemonic.Pcmpgtb or Mnemonic.Pcmpgtw or Mnemonic.Pcmpgtd)
                    value = b.Sext(b.Slt(c, a), width);
                else if (instruction.Mnemonic is Mnemonic.Pminub or Mnemonic.Pmaxub or Mnemonic.Pminsw or Mnemonic.Pmaxsw)
                {
                    Value less = width == 8 ? b.Ult(a, c) : b.Slt(a, c);
                    bool minimum = instruction.Mnemonic is Mnemonic.Pminub or Mnemonic.Pminsw;
                    value = b.Select(less, minimum ? a : c, minimum ? c : a);
                }
                else if (instruction.Mnemonic is Mnemonic.Pmullw or Mnemonic.Pmulhw or Mnemonic.Pmulhuw)
                {
                    bool signed = instruction.Mnemonic == Mnemonic.Pmulhw;
                    Value product = b.Mul(Resize(a, 32, signed), Resize(c, 32, signed));
                    value = b.Extract(product, instruction.Mnemonic == Mnemonic.Pmullw ? 0 : 16, 16);
                }
                else if (saturate)
                {
                    // N+2 位保留无符号减法的负值及加法进位，随后按区间截断。
                    int wide = width + 2;
                    Value aa = Resize(a, wide, !unsigned), cc = Resize(c, wide, !unsigned);
                    Value sum = subtract ? b.Sub(aa, cc) : b.Add(aa, cc);
                    Value minimum = unsigned ? b.Const(wide, 0) : b.Sext(b.Const(width, 1UL << (width - 1)), wide);
                    Value maximum = b.Const(wide, unsigned ? (1UL << width) - 1 : (1UL << (width - 1)) - 1);
                    value = b.Trunc(b.Select(b.Slt(sum, minimum), minimum, b.Select(b.Slt(maximum, sum), maximum, sum)), width);
                }
                else value = subtract ? b.Sub(a, c) : b.Add(a, c);
                lanes.Add(value);
            }
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult PackedLaneShift()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !(instruction.Op1Kind == OpKind.Immediate8 || IsSimdSource(1)))
                return Unsupported("packed lane 移位需要 XMM 与 imm8/XMM/m128");
            SimdAlignment();
            int width = instruction.Mnemonic is Mnemonic.Psllw or Mnemonic.Psrlw or Mnemonic.Psraw ? 16
                : instruction.Mnemonic is Mnemonic.Psllq or Mnemonic.Psrlq ? 64 : 32;
            Value source = ReadXmm(0);
            Value count = instruction.Op1Kind == OpKind.Immediate8 ? b.Const(64, instruction.Immediate8) : b.Trunc(ReadSimdSource(1, 128), 64);
            List<Value> lanes = [];
            for (int offset = 0; offset < 128; offset += width)
            {
                Value lane = b.Extract(source, offset, width);
                lanes.Add(instruction.Mnemonic is Mnemonic.Psllw or Mnemonic.Pslld or Mnemonic.Psllq ? b.Shl(lane, count)
                    : instruction.Mnemonic is Mnemonic.Psraw or Mnemonic.Psrad ? b.Sar(lane, count) : b.Shr(lane, count));
            }
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }
    }
}
