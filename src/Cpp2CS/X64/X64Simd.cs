using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private bool IsXmm(int operand) => instruction.GetOpKind(operand) == OpKind.Register &&
            instruction.GetOpRegister(operand) is >= Register.XMM0 and <= Register.XMM15;

        private bool IsSimdMemory(int operand, int width) => instruction.GetOpKind(operand) == OpKind.Memory &&
            instruction.MemorySize.GetSize() * 8 == width && ValidAddress();

        private bool IsSimdSource(int operand, int memoryWidth = 128) => IsXmm(operand) || IsSimdMemory(operand, memoryWidth);

        private Value ReadXmm(int operand) => b.Read(instruction.GetOpRegister(operand).ToString().ToLowerInvariant(), 128);
        private void WriteXmm(int operand, Value value) => b.Write(instruction.GetOpRegister(operand).ToString().ToLowerInvariant(), value);
        private Value ReadSimdSource(int operand, int width) => IsXmm(operand)
            ? Resize(ReadXmm(operand), width) : b.Load(Address(), width);

        private void SimdAlignment()
        {
            if (instruction.Op0Kind == OpKind.Memory || instruction.Op1Kind == OpKind.Memory)
                b.Guard(b.Eq(b.And(Address(), b.Const(64, 15)), b.Const(64, 0)), "legacy SSE 16-byte alignment #GP is an unmodeled fault stop");
        }

        private LiftResult PackedMove()
        {
            if (instruction.OpCount != 2 ||
                !(IsXmm(0) && IsSimdSource(1) || IsSimdMemory(0, 128) && IsXmm(1)))
                return Unsupported("128 位 XMM 搬运形式未支持");
            if (instruction.Mnemonic is Mnemonic.Movaps or Mnemonic.Movapd or Mnemonic.Movdqa)
                SimdAlignment();
            Value source = ReadSimdSource(1, 128);
            if (IsXmm(0)) WriteXmm(0, source);
            else b.Store(Address(), source);
            return Next();
        }

        private LiftResult ScalarSimdMove()
        {
            int width = instruction.Mnemonic == Mnemonic.Movss ? 32 : 64;
            if (instruction.OpCount != 2 ||
                !(IsXmm(0) && IsSimdSource(1, width) || IsSimdMemory(0, width) && IsXmm(1)))
                return Unsupported("仅支持 legacy SSE 标量搬运，不支持字符串 MOVSD");
            Value source = ReadSimdSource(1, width);
            if (IsXmm(0))
            {
                Value value = IsXmm(1) ? b.Concat(b.Extract(ReadXmm(0), width, 128 - width), source) : b.Zext(source, 128);
                WriteXmm(0, value);
            }
            else b.Store(Address(), source);
            return Next();
        }

        private LiftResult IntegerSimdMove()
        {
            int width = instruction.Mnemonic == Mnemonic.Movd ? 32 : 64;
            bool IntegerSource(int operand) => IsSimdMemory(operand, width) ||
                instruction.GetOpKind(operand) == OpKind.Register && instruction.GetOpRegister(operand).IsGPR() && Width(operand) == width;
            if (instruction.OpCount != 2 ||
                !(IsXmm(0) && (IntegerSource(1) || width == 64 && IsXmm(1)) || IntegerSource(0) && IsXmm(1)))
                return Unsupported("MOVD/MOVQ 仅支持 XMM 与普通整数操作数，不支持 MMX");
            Value source = IsXmm(1) ? b.Trunc(ReadXmm(1), width) : ReadOperand(1, width);
            if (IsXmm(0)) WriteXmm(0, b.Zext(source, 128));
            else WriteOperand(0, source);
            return Next();
        }

        private LiftResult HalfSimdMove()
        {
            if (instruction.OpCount != 2) return Unsupported("半寄存器搬运操作数数量无效");
            bool high = instruction.Mnemonic is Mnemonic.Movhps or Mnemonic.Movhpd or Mnemonic.Movlhps;
            if (instruction.Mnemonic is Mnemonic.Movhlps or Mnemonic.Movlhps)
            {
                if (!IsXmm(0) || !IsXmm(1)) return Unsupported("MOVHLPS/MOVLHPS 需要 XMM 操作数");
                Value old = ReadXmm(0), source = ReadXmm(1);
                WriteXmm(0, high ? b.Concat(b.Trunc(source, 64), b.Trunc(old, 64))
                    : b.Concat(b.Extract(old, 64, 64), b.Extract(source, 64, 64)));
            }
            else if (IsXmm(0) && IsSimdMemory(1, 64))
            {
                Value source = b.Load(Address(), 64), old = ReadXmm(0);
                WriteXmm(0, high ? b.Concat(source, b.Trunc(old, 64)) : b.Concat(b.Extract(old, 64, 64), source));
            }
            else if (IsSimdMemory(0, 64) && IsXmm(1))
                b.Store(Address(), b.Extract(ReadXmm(1), high ? 64 : 0, 64));
            else return Unsupported("MOVLPS/MOVHPS/MOVLPD/MOVHPD 需要一个 64 位内存操作数");
            return Next();
        }

        private LiftResult PackedLogical()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1))
                return Unsupported("位逻辑仅支持 XMM 与 128 位来源");
            SimdAlignment();
            Value left = ReadXmm(0), right = ReadSimdSource(1, 128);
            Value result = instruction.Mnemonic switch
            {
                Mnemonic.Andps or Mnemonic.Andpd or Mnemonic.Pand => b.And(left, right),
                Mnemonic.Andnps or Mnemonic.Andnpd or Mnemonic.Pandn => b.And(b.Not(left), right),
                Mnemonic.Orps or Mnemonic.Orpd or Mnemonic.Por => b.Or(left, right),
                _ => b.Xor(left, right)
            };
            WriteXmm(0, result);
            return Next();
        }

        private Value PackLanes(IReadOnlyList<Value> lowToHigh)
        {
            Value result = lowToHigh[0];
            for (int index = 1; index < lowToHigh.Count; index++) result = b.Concat(lowToHigh[index], result);
            return result;
        }

        private LiftResult PackedShuffle()
        {
            if (instruction.OpCount != 3 || !IsXmm(0) || !IsSimdSource(1) || instruction.Op2Kind != OpKind.Immediate8)
                return Unsupported("重排仅支持 XMM、128 位来源与 imm8");
            SimdAlignment();
            Value source = ReadSimdSource(1, 128);
            int control = instruction.Immediate8;
            List<Value> lanes = [];
            if (instruction.Mnemonic is Mnemonic.Shufps or Mnemonic.Shufpd)
            {
                Value old = ReadXmm(0);
                int width = instruction.Mnemonic == Mnemonic.Shufps ? 32 : 64;
                int count = 128 / width, selectorBits = width == 32 ? 2 : 1;
                for (int index = 0; index < count; index++)
                    lanes.Add(b.Extract(index < count / 2 ? old : source,
                        ((control >> (selectorBits * index)) & (count - 1)) * width, width));
            }
            else if (instruction.Mnemonic == Mnemonic.Pshufd)
            {
                for (int index = 0; index < 4; index++) lanes.Add(b.Extract(source, ((control >> (index * 2)) & 3) * 32, 32));
            }
            else
            {
                int half = instruction.Mnemonic == Mnemonic.Pshufhw ? 4 : 0;
                for (int index = 0; index < 8; index++)
                {
                    int lane = index >= half && index < half + 4 ? half + ((control >> ((index - half) * 2)) & 3) : index;
                    lanes.Add(b.Extract(source, lane * 16, 16));
                }
            }
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult PackedUnpack()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1))
                return Unsupported("交错仅支持 XMM 与 128 位来源");
            SimdAlignment();
            int width = instruction.Mnemonic switch
            {
                Mnemonic.Punpcklbw or Mnemonic.Punpckhbw => 8,
                Mnemonic.Punpcklwd or Mnemonic.Punpckhwd => 16,
                Mnemonic.Unpcklpd or Mnemonic.Unpckhpd or Mnemonic.Punpcklqdq or Mnemonic.Punpckhqdq => 64,
                _ => 32
            };
            bool high = instruction.Mnemonic is Mnemonic.Unpckhps or Mnemonic.Unpckhpd
                or Mnemonic.Punpckhbw or Mnemonic.Punpckhwd or Mnemonic.Punpckhdq or Mnemonic.Punpckhqdq;
            Value left = ReadXmm(0), right = ReadSimdSource(1, 128);
            List<Value> lanes = [];
            for (int offset = high ? 64 : 0; offset < (high ? 128 : 64); offset += width)
            {
                lanes.Add(b.Extract(left, offset, width));
                lanes.Add(b.Extract(right, offset, width));
            }
            WriteXmm(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult PackedByteShift()
        {
            if (instruction.OpCount != 2 || !IsXmm(0) || instruction.Op1Kind != OpKind.Immediate8)
                return Unsupported("字节移位需要 XMM 与 imm8");
            Value source = ReadXmm(0), count = b.Const(16, (ulong)instruction.Immediate8 * 8);
            WriteXmm(0, instruction.Mnemonic == Mnemonic.Psrldq ? b.Shr(source, count) : b.Shl(source, count));
            return Next();
        }

        private LiftResult PackedMask()
        {
            if (instruction.OpCount != 2 || instruction.Op0Kind != OpKind.Register ||
                !(instruction.Op0Register.IsGPR32() || instruction.Mnemonic == Mnemonic.Pmovmskb && instruction.Op0Register.IsGPR64()) || !IsXmm(1))
                return Unsupported("符号位提取需要 r32（PMOVMSKB 也支持 r64）与 XMM");
            int width = instruction.Mnemonic == Mnemonic.Pmovmskb ? 8 : instruction.Mnemonic == Mnemonic.Movmskps ? 32 : 64;
            Value source = ReadXmm(1);
            List<Value> bits = [];
            for (int offset = width - 1; offset < 128; offset += width) bits.Add(b.Extract(source, offset, 1));
            WriteRegister(instruction.Op0Register, b.Zext(PackLanes(bits), Width(0)));
            return Next();
        }

        private LiftResult ExtractWord()
        {
            // SSE2 0F C5；SSE4.1 的 0F 3A 15 形式不在当前 profile 内。
            if (instruction.Code != Code.Pextrw_r32_xmm_imm8 || !IsXmm(1))
                return Unsupported("PEXTRW 仅支持 SSE2 r32,xmm,imm8");
            WriteRegister(instruction.Op0Register, b.Zext(b.Extract(ReadXmm(1), (instruction.Immediate8 & 7) * 16, 16), 32));
            return Next();
        }
    }
}
