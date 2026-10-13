using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private LiftResult PackedInteger()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1)) return Unsupported("packed 整数运算仅支持 legacy XMM 形式");
            SimdAlignment();
            int width = instruction.Mnemonic switch
            {
                Mnemonic.Paddb or Mnemonic.Psubb or Mnemonic.Paddsb or Mnemonic.Paddusb or Mnemonic.Psubsb or Mnemonic.Psubusb
                    or Mnemonic.Pcmpeqb or Mnemonic.Pcmpgtb or Mnemonic.Pminub or Mnemonic.Pmaxub or Mnemonic.Pminsb or Mnemonic.Pmaxsb => 8,
                Mnemonic.Paddd or Mnemonic.Psubd or Mnemonic.Pcmpeqd or Mnemonic.Pcmpgtd
                    or Mnemonic.Pminsd or Mnemonic.Pmaxsd or Mnemonic.Pminud or Mnemonic.Pmaxud or Mnemonic.Pmulld => 32,
                Mnemonic.Paddq or Mnemonic.Psubq or Mnemonic.Pcmpeqq => 64,
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
                if (instruction.Mnemonic is Mnemonic.Pcmpeqb or Mnemonic.Pcmpeqw or Mnemonic.Pcmpeqd or Mnemonic.Pcmpeqq)
                    value = b.Sext(b.Eq(a, c), width);
                else if (instruction.Mnemonic is Mnemonic.Pcmpgtb or Mnemonic.Pcmpgtw or Mnemonic.Pcmpgtd)
                    value = b.Sext(b.Slt(c, a), width);
                else if (instruction.Mnemonic is Mnemonic.Pminub or Mnemonic.Pmaxub or Mnemonic.Pminsw or Mnemonic.Pmaxsw
                    or Mnemonic.Pminsb or Mnemonic.Pmaxsb or Mnemonic.Pminuw or Mnemonic.Pmaxuw
                    or Mnemonic.Pminsd or Mnemonic.Pmaxsd or Mnemonic.Pminud or Mnemonic.Pmaxud)
                {
                    bool unsignedCompare = instruction.Mnemonic is Mnemonic.Pminub or Mnemonic.Pmaxub or Mnemonic.Pminuw or Mnemonic.Pmaxuw or Mnemonic.Pminud or Mnemonic.Pmaxud;
                    Value less = unsignedCompare ? b.Ult(a, c) : b.Slt(a, c);
                    bool minimum = instruction.Mnemonic is Mnemonic.Pminub or Mnemonic.Pminsw or Mnemonic.Pminsb or Mnemonic.Pminuw or Mnemonic.Pminsd or Mnemonic.Pminud;
                    value = b.Select(less, minimum ? a : c, minimum ? c : a);
                }
                else if (instruction.Mnemonic == Mnemonic.Pmulld) value = b.Mul(a, c);
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

        private LiftResult PackedShuffleBytes()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1)) return Unsupported("PSHUFB 仅支持 legacy XMM 形式");
            SimdAlignment();
            Value source = ReadXmm(0), control = ReadSimdSource(1, 128);
            List<Value> lanes = [];
            for (int offset = 0; offset < 128; offset += 8)
            {
                Value index = b.Extract(control, offset, 4);
                Value shift = b.Mul(b.Zext(index, 8), b.Const(8, 8));
                Value selected = b.Trunc(b.Shr(source, shift), 8);
                lanes.Add(b.Select(b.Extract(control, offset + 7, 1), b.Const(8, 0), selected));
            }
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult PackedExtend()
        {
            (int from, int to) = instruction.Mnemonic switch
            {
                Mnemonic.Pmovsxbw or Mnemonic.Pmovzxbw => (8, 16),
                Mnemonic.Pmovsxbd or Mnemonic.Pmovzxbd => (8, 32),
                Mnemonic.Pmovsxbq or Mnemonic.Pmovzxbq => (8, 64),
                Mnemonic.Pmovsxwd or Mnemonic.Pmovzxwd => (16, 32),
                Mnemonic.Pmovsxwq or Mnemonic.Pmovzxwq => (16, 64),
                _ => (32, 64)
            };
            int count = 128 / to, memoryWidth = count * from;
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1, memoryWidth)) return Unsupported("PMOVSX/ZX 来源宽度未支持");
            bool signed = instruction.Mnemonic is Mnemonic.Pmovsxbw or Mnemonic.Pmovsxbd or Mnemonic.Pmovsxbq
                or Mnemonic.Pmovsxwd or Mnemonic.Pmovsxwq or Mnemonic.Pmovsxdq;
            Value source = ReadSimdSource(1, memoryWidth);
            List<Value> lanes = [];
            for (int index = 0; index < count; index++) lanes.Add(Resize(b.Extract(source, index * from, from), to, signed));
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult PackedTest()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1)) return Unsupported("PTEST 仅支持 legacy XMM 形式");
            SimdAlignment();
            Value left = ReadXmm(0), right = ReadSimdSource(1, 128), zero = b.Const(128, 0);
            b.Write("zf", b.Eq(b.And(left, right), zero));
            b.Write("cf", b.Eq(b.And(b.Not(left), right), zero));
            foreach (string flag in new[] { "of", "sf", "af", "pf" }) b.Write(flag, b.Const(1, 0));
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
