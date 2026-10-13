using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private string VectorName => instruction.Mnemonic.ToString()[1..].ToLowerInvariant();
        private bool IsVector(int operand, int width = 0) => operand < instruction.OpCount && instruction.GetOpKind(operand) == OpKind.Register &&
            (instruction.GetOpRegister(operand) is >= Register.XMM0 and <= Register.XMM15 or >= Register.YMM0 and <= Register.YMM15) &&
            (width == 0 || Width(operand) == width);
        private bool IsVectorSource(int operand, int width) => IsVector(operand, width) || IsSimdMemory(operand, width);
        private int VectorIndex(int operand) => (int)instruction.GetOpRegister(operand) - (int)(Width(operand) == 256 ? Register.YMM0 : Register.XMM0);
        private Value ReadVector(int operand)
        {
            int index = VectorIndex(operand);
            Value low = b.Read($"xmm{index}", 128);
            return Width(operand) == 128 ? low : b.Concat(b.Read($"ymm{index}_hi", 128), low);
        }
        private Value VectorSource(int operand, int width) => IsVector(operand) ? Resize(ReadVector(operand), width) : b.Load(Address(), width);
        private void WriteVector(int operand, Value value)
        {
            int index = VectorIndex(operand);
            b.Write($"xmm{index}", b.Trunc(value, 128));
            b.Write($"ymm{index}_hi", value.Width == 256 ? b.Extract(value, 128, 128) : b.Const(128, 0));
        }
        private void VectorAlignment(int bytes)
        {
            b.Guard(b.Eq(b.And(Address(), b.Const(64, (ulong)bytes - 1)), b.Const(64, 0)), "aligned AVX memory operand #GP is an unmodeled fault stop");
        }

        internal LiftResult Avx() => VectorName switch
        {
            "movaps" or "movapd" or "movups" or "movupd" or "movdqa" or "movdqu" => AvxMove(),
            "movntdq" or "movntps" or "movntpd" => AvxNonTemporalStore(),
            "pmaskmovd" or "pmaskmovq" => AvxMaskedMemory(),
            "movss" or "movsd" => AvxScalarMove(),
            "movd" or "movq" => AvxIntegerMove(),
            "zeroupper" or "zeroall" => AvxZero(),
            "andps" or "andpd" or "andnps" or "andnpd" or "orps" or "orpd" or "xorps" or "xorpd"
                or "pand" or "pandn" or "por" or "pxor" => AvxLogical(),
            "paddb" or "paddw" or "paddd" or "paddq" or "psubb" or "psubw" or "psubd" or "psubq"
                or "paddsb" or "paddsw" or "paddusb" or "paddusw" or "psubsb" or "psubsw" or "psubusb" or "psubusw"
                or "pcmpeqb" or "pcmpeqw" or "pcmpeqd" or "pcmpeqq" or "pcmpgtb" or "pcmpgtw" or "pcmpgtd" or "pcmpgtq"
                or "pminsb" or "pminsw" or "pminsd" or "pminub" or "pminuw" or "pminud"
                or "pmaxsb" or "pmaxsw" or "pmaxsd" or "pmaxub" or "pmaxuw" or "pmaxud"
                or "pmullw" or "pmulld" or "pmulhw" or "pmulhuw" => AvxInteger(),
            "psllw" or "pslld" or "psllq" or "psrlw" or "psrld" or "psrlq" or "psraw" or "psrad"
                or "psllvd" or "psllvq" or "psrlvd" or "psrlvq" or "psravd" => AvxShift(),
            "pslldq" or "psrldq" => AvxByteShift(),
            "pshufd" or "pshuflw" or "pshufhw" or "shufps" or "shufpd" => AvxShuffle(),
            "pshufb" => AvxShuffleBytes(),
            "punpcklbw" or "punpckhbw" or "punpcklwd" or "punpckhwd" or "punpckldq" or "punpckhdq"
                or "punpcklqdq" or "punpckhqdq" or "unpcklps" or "unpckhps" or "unpcklpd" or "unpckhpd" => AvxUnpack(),
            "pmovsxbw" or "pmovsxbd" or "pmovsxbq" or "pmovsxwd" or "pmovsxwq" or "pmovsxdq"
                or "pmovzxbw" or "pmovzxbd" or "pmovzxbq" or "pmovzxwd" or "pmovzxwq" or "pmovzxdq" => AvxExtend(),
            "movmskps" or "movmskpd" or "pmovmskb" => AvxMask(),
            "insertf128" or "inserti128" or "extractf128" or "extracti128" => AvxHalf(),
            "addss" or "addsd" or "addps" or "addpd" or "subss" or "subsd" or "subps" or "subpd"
                or "mulss" or "mulsd" or "mulps" or "mulpd" or "divss" or "divsd" or "divps" or "divpd"
                or "sqrtss" or "sqrtsd" or "sqrtps" or "sqrtpd" or "minss" or "minsd" or "minps" or "minpd"
                or "maxss" or "maxsd" or "maxps" or "maxpd" => AvxFloatArithmetic(),
            "comiss" or "comisd" or "ucomiss" or "ucomisd" => AvxFloatFlags(),
            "cmpss" or "cmpsd" or "cmpps" or "cmppd" => AvxFloatMask(),
            "cvtsi2ss" or "cvtsi2sd" or "cvtss2si" or "cvtsd2si" or "cvttss2si" or "cvttsd2si" or "cvtss2sd" or "cvtsd2ss" => AvxFloatScalarConvert(),
            "cvtdq2ps" or "cvtdq2pd" or "cvtps2pd" or "cvtpd2ps" or "cvtps2dq" or "cvttps2dq" or "cvtpd2dq" or "cvttpd2dq" => AvxFloatPackedConvert(),
            "ldmxcsr" or "stmxcsr" => AvxMxcsr(),
            "roundss" or "roundsd" or "roundps" or "roundpd" => AvxRound(),
            "pcmpistri" => CompareImplicitStrings(),
            _ when VectorName.StartsWith("fmadd", StringComparison.Ordinal) || VectorName.StartsWith("fmsub", StringComparison.Ordinal)
                || VectorName.StartsWith("fnmadd", StringComparison.Ordinal) || VectorName.StartsWith("fnmsub", StringComparison.Ordinal) => AvxFused(),
            _ => Unsupported("该 AVX 指令尚无完整语义规则")
        };

        private LiftResult AvxMove()
        {
            int width = IsVector(0) ? Width(0) : IsVector(1) ? Width(1) : 0;
            if (instruction.OpCount != 2 || width == 0 || !(IsVector(0, width) && IsVectorSource(1, width) || IsSimdMemory(0, width) && IsVector(1, width)))
                return Unsupported("AVX 向量搬运操作数不匹配");
            if (VectorName is "movaps" or "movapd" or "movdqa" && (instruction.Op0Kind == OpKind.Memory || instruction.Op1Kind == OpKind.Memory))
                VectorAlignment(width / 8);
            Value source = VectorSource(1, width);
            if (IsVector(0)) WriteVector(0, source); else b.Store(Address(), source);
            return Next();
        }

        private LiftResult AvxMaskedMemory()
        {
            bool store = instruction.Op0Kind == OpKind.Memory;
            int vectorOperand = store ? 2 : 0, memoryOperand = store ? 0 : 2;
            if (instruction.OpCount != 3 || !IsVector(vectorOperand) || !IsVector(1, Width(vectorOperand)) ||
                !IsSimdMemory(memoryOperand, Width(vectorOperand)))
                return Unsupported("VPMASKMOV 操作数未支持");
            int width = VectorName.EndsWith('q') ? 64 : 32, totalWidth = Width(vectorOperand);
            Value mask = ReadVector(1), address = Address();
            Value? source = store ? ReadVector(vectorOperand) : null;
            List<Value> lanes = [];
            for (int offset = 0; offset < totalWidth; offset += width)
            {
                Value active = b.Extract(mask, offset + width - 1, 1), location = b.Add(address, b.Const(64, (ulong)(offset / 8)));
                Value end = b.Add(location, b.Const(64, (ulong)(width / 8 - 1)));
                Value canonical = b.And(b.Eq(location, b.Sext(b.Trunc(location, 48), 64)), b.Eq(end, b.Sext(b.Trunc(end, 48), 64)));
                b.Guard(b.Or(b.BoolNot(active), canonical), "active masked memory lane noncanonical address is an unmodeled fault stop");
                if (store) b.StoreIf(active, location, b.Extract(source!.Value, offset, width));
                else lanes.Add(b.LoadIf(active, location, width));
            }
            if (!store) WriteVector(vectorOperand, PackLanes(lanes));
            b.MarkNormalPathOnly("masked lanes retain conditional memory effects; hardware access ordering and fault partial-state delivery are unmodeled");
            return Next();
        }

        private LiftResult AvxScalarMove()
        {
            int width = VectorName == "movss" ? 32 : 64;
            if (instruction.OpCount == 3 && IsVector(0, 128) && IsVector(1, 128) && IsVector(2, 128))
                WriteVector(0, b.Concat(b.Extract(ReadVector(1), width, 128 - width), b.Trunc(ReadVector(2), width)));
            else if (instruction.OpCount == 2 && IsVector(0, 128) && IsSimdMemory(1, width))
                WriteVector(0, b.Zext(b.Load(Address(), width), 128));
            else if (instruction.OpCount == 2 && IsSimdMemory(0, width) && IsVector(1, 128))
                b.Store(Address(), b.Trunc(ReadVector(1), width));
            else return Unsupported("AVX 标量搬运操作数不匹配");
            return Next();
        }

        private LiftResult AvxNonTemporalStore()
        {
            if (instruction.OpCount != 2 || !IsVector(1) || !IsSimdMemory(0, Width(1)))
                return Unsupported("AVX non-temporal store 操作数未支持");
            int width = Width(1);
            VectorAlignment(width / 8);
            b.Store(Address(), ReadVector(1), new(MemoryOrder.Relaxed, width, 0, NonTemporal: true));
            b.MarkNormalPathOnly("non-temporal policy is retained as an event; cache and concurrent visibility are outside the byte-state interpreter", ObligationKind.CacheEffects);
            return Next();
        }

        private LiftResult AvxIntegerMove()
        {
            int width = VectorName == "movd" ? 32 : 64;
            bool Integer(int index) => IsSimdMemory(index, width) || instruction.GetOpKind(index) == OpKind.Register && instruction.GetOpRegister(index).IsGPR() && Width(index) == width;
            if (instruction.OpCount != 2 || !(IsVector(0, 128) && (Integer(1) || width == 64 && IsVector(1, 128)) || Integer(0) && IsVector(1, 128)))
                return Unsupported("AVX MOVD/MOVQ 操作数不匹配");
            Value value = IsVector(1) ? b.Trunc(ReadVector(1), width) : ReadOperand(1, width);
            if (IsVector(0)) WriteVector(0, b.Zext(value, 128)); else WriteOperand(0, value);
            return Next();
        }

        private LiftResult AvxZero()
        {
            for (int index = 0; index < 16; index++)
            {
                if (VectorName == "zeroall") b.Write($"xmm{index}", b.Const(128, 0));
                b.Write($"ymm{index}_hi", b.Const(128, 0));
            }
            return Next();
        }

        private bool VectorBinary() => instruction.OpCount == 3 && IsVector(0) && IsVector(1, Width(0)) && IsVectorSource(2, Width(0));
        private LiftResult AvxLogical()
        {
            if (!VectorBinary()) return Unsupported("AVX 位逻辑操作数不匹配");
            Value left = ReadVector(1), right = VectorSource(2, Width(0));
            Value value = VectorName switch
            {
                "andps" or "andpd" or "pand" => b.And(left, right),
                "andnps" or "andnpd" or "pandn" => b.And(b.Not(left), right),
                "orps" or "orpd" or "por" => b.Or(left, right),
                _ => b.Xor(left, right)
            };
            WriteVector(0, value);
            return Next();
        }

        private LiftResult AvxInteger()
        {
            if (!VectorBinary()) return Unsupported("AVX packed 整数操作数不匹配");
            string name = VectorName;
            int width = name.EndsWith('b') ? 8 : name.EndsWith('d') ? 32 : name.EndsWith('q') ? 64 : 16;
            Value left = ReadVector(1), right = VectorSource(2, Width(0));
            List<Value> lanes = [];
            for (int offset = 0; offset < left.Width; offset += width)
            {
                Value a = b.Extract(left, offset, width), c = b.Extract(right, offset, width), value;
                if (name.StartsWith("pcmpeq", StringComparison.Ordinal)) value = b.Sext(b.Eq(a, c), width);
                else if (name.StartsWith("pcmpgt", StringComparison.Ordinal)) value = b.Sext(b.Slt(c, a), width);
                else if (name.StartsWith("pmin", StringComparison.Ordinal) || name.StartsWith("pmax", StringComparison.Ordinal))
                {
                    Value less = name[4] == 'u' ? b.Ult(a, c) : b.Slt(a, c);
                    value = name[1..4] == "min" ? b.Select(less, a, c) : b.Select(less, c, a);
                }
                else if (name is "pmullw" or "pmulld") value = b.Mul(a, c);
                else if (name is "pmulhw" or "pmulhuw")
                    value = b.Extract(b.Mul(Resize(a, 32, name == "pmulhw"), Resize(c, 32, name == "pmulhw")), 16, 16);
                else
                {
                    bool subtract = name.StartsWith("psub", StringComparison.Ordinal);
                    bool saturate = name.Length > 5;
                    if (!saturate) value = subtract ? b.Sub(a, c) : b.Add(a, c);
                    else
                    {
                        bool unsigned = name.Contains("us", StringComparison.Ordinal);
                        int wide = width + 2;
                        Value aa = Resize(a, wide, !unsigned), cc = Resize(c, wide, !unsigned);
                        Value sum = subtract ? b.Sub(aa, cc) : b.Add(aa, cc);
                        Value minimum = unsigned ? b.Const(wide, 0) : b.Sext(b.Const(width, 1UL << (width - 1)), wide);
                        Value maximum = b.Const(wide, unsigned ? (1UL << width) - 1 : (1UL << (width - 1)) - 1);
                        value = b.Trunc(b.Select(b.Slt(sum, minimum), minimum, b.Select(b.Slt(maximum, sum), maximum, sum)), width);
                    }
                }
                lanes.Add(value);
            }
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxShift()
        {
            bool variable = VectorName.Contains('v');
            if (instruction.OpCount != 3 || !IsVector(0) || !IsVector(1, Width(0)) ||
                !(variable ? IsVectorSource(2, Width(0)) : instruction.Op2Kind == OpKind.Immediate8 || IsVectorSource(2, 128)))
                return Unsupported("AVX lane 移位操作数不匹配");
            int width = VectorName.EndsWith('w') ? 16 : VectorName.EndsWith('q') ? 64 : 32;
            Value source = ReadVector(1);
            Value count = instruction.Op2Kind == OpKind.Immediate8 ? b.Const(64, instruction.Immediate8)
                : variable ? VectorSource(2, Width(0)) : b.Trunc(VectorSource(2, 128), 64);
            List<Value> lanes = [];
            for (int offset = 0; offset < source.Width; offset += width)
            {
                Value lane = b.Extract(source, offset, width), shift = variable ? b.Extract(count, offset, width) : count;
                lanes.Add(VectorName.StartsWith("psll", StringComparison.Ordinal) ? b.Shl(lane, shift)
                    : VectorName.StartsWith("psra", StringComparison.Ordinal) ? b.Sar(lane, shift) : b.Shr(lane, shift));
            }
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxByteShift()
        {
            if (instruction.OpCount != 3 || !IsVector(0) || !IsVector(1, Width(0)) || instruction.Op2Kind != OpKind.Immediate8)
                return Unsupported("AVX 字节移位操作数不匹配");
            Value source = ReadVector(1), count = b.Const(16, (ulong)instruction.Immediate8 * 8);
            List<Value> halves = [];
            for (int offset = 0; offset < source.Width; offset += 128)
            {
                Value half = b.Extract(source, offset, 128);
                halves.Add(VectorName == "pslldq" ? b.Shl(half, count) : b.Shr(half, count));
            }
            WriteVector(0, PackLanes(halves));
            return Next();
        }

        private LiftResult AvxShuffle()
        {
            bool two = VectorName is "shufps" or "shufpd";
            int sourceOperand = two ? 2 : 1;
            if (instruction.OpCount != (two ? 4 : 3) || !IsVector(0) || !IsVectorSource(sourceOperand, Width(0)) ||
                two && !IsVector(1, Width(0)) || instruction.GetOpKind(sourceOperand + 1) != OpKind.Immediate8)
                return Unsupported("AVX shuffle 操作数不匹配");
            Value right = VectorSource(sourceOperand, Width(0)), left = two ? ReadVector(1) : right;
            int control = instruction.Immediate8;
            List<Value> lanes = [];
            for (int half = 0; half < right.Width; half += 128)
            {
                int width = VectorName == "shufpd" ? 64 : VectorName is "pshufhw" or "pshuflw" ? 16 : 32;
                int count = 128 / width;
                for (int index = 0; index < count; index++)
                {
                    int selected;
                    if (width == 16)
                    {
                        int start = VectorName == "pshufhw" ? 4 : 0;
                        selected = index >= start && index < start + 4 ? start + ((control >> ((index - start) * 2)) & 3) : index;
                    }
                    else if (width == 64) selected = (control >> (half / 64 + index)) & 1;
                    else selected = (control >> (index * 2)) & 3;
                    lanes.Add(b.Extract(two && index < count / 2 ? left : right, half + selected * width, width));
                }
            }
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxShuffleBytes()
        {
            if (!VectorBinary()) return Unsupported("AVX PSHUFB 操作数不匹配");
            Value source = ReadVector(1), control = VectorSource(2, Width(0));
            List<Value> lanes = [];
            for (int offset = 0; offset < source.Width; offset += 8)
            {
                Value index = b.Mul(b.Zext(b.Extract(control, offset, 4), 8), b.Const(8, 8));
                Value selected = b.Trunc(b.Shr(b.Extract(source, offset / 128 * 128, 128), index), 8);
                lanes.Add(b.Select(b.Extract(control, offset + 7, 1), b.Const(8, 0), selected));
            }
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxUnpack()
        {
            if (!VectorBinary()) return Unsupported("AVX unpack 操作数不匹配");
            string name = VectorName;
            int width = name.EndsWith("bw", StringComparison.Ordinal) ? 8 : name.EndsWith("wd", StringComparison.Ordinal) ? 16
                : name.EndsWith("qdq", StringComparison.Ordinal) || name.EndsWith("pd", StringComparison.Ordinal) ? 64 : 32;
            bool high = name.Contains("ckh", StringComparison.Ordinal);
            Value left = ReadVector(1), right = VectorSource(2, Width(0));
            List<Value> lanes = [];
            for (int half = 0; half < left.Width; half += 128)
                for (int offset = high ? 64 : 0; offset < (high ? 128 : 64); offset += width)
                {
                    lanes.Add(b.Extract(left, half + offset, width));
                    lanes.Add(b.Extract(right, half + offset, width));
                }
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxExtend()
        {
            (int from, int to) = VectorName[^2..] switch { "bw" => (8, 16), "bd" => (8, 32), "bq" => (8, 64), "wd" => (16, 32), "wq" => (16, 64), _ => (32, 64) };
            if (instruction.OpCount != 2 || !IsVector(0)) return Unsupported("AVX PMOVSX/ZX 目的未支持");
            int count = Width(0) / to, memoryWidth = count * from;
            if (!(IsVector(1, 128) || IsSimdMemory(1, memoryWidth))) return Unsupported("AVX PMOVSX/ZX 来源未支持");
            Value source = VectorSource(1, memoryWidth);
            List<Value> lanes = [];
            for (int index = 0; index < count; index++) lanes.Add(Resize(b.Extract(source, index * from, from), to, VectorName.StartsWith("pmovsx", StringComparison.Ordinal)));
            WriteVector(0, PackLanes(lanes));
            return Next();
        }

        private LiftResult AvxMask()
        {
            if (instruction.OpCount != 2 || instruction.Op0Kind != OpKind.Register || !instruction.Op0Register.IsGPR32() || !IsVector(1))
                return Unsupported("AVX mask 操作数未支持");
            int width = VectorName == "pmovmskb" ? 8 : VectorName == "movmskps" ? 32 : 64;
            Value source = ReadVector(1);
            List<Value> bits = [];
            for (int offset = width - 1; offset < source.Width; offset += width) bits.Add(b.Extract(source, offset, 1));
            WriteRegister(instruction.Op0Register, b.Zext(PackLanes(bits), 32));
            return Next();
        }

        private LiftResult AvxHalf()
        {
            bool insert = VectorName.StartsWith("insert", StringComparison.Ordinal);
            if (insert)
            {
                if (instruction.OpCount != 4 || !IsVector(0, 256) || !IsVector(1, 256) || !IsVectorSource(2, 128) || instruction.Op3Kind != OpKind.Immediate8)
                    return Unsupported("AVX insert128 操作数未支持");
                Value source = ReadVector(1), half = VectorSource(2, 128);
                WriteVector(0, (instruction.Immediate8 & 1) == 0 ? b.Concat(b.Extract(source, 128, 128), half) : b.Concat(half, b.Trunc(source, 128)));
            }
            else
            {
                if (instruction.OpCount != 3 || !(IsVector(0, 128) || IsSimdMemory(0, 128)) || !IsVector(1, 256) || instruction.Op2Kind != OpKind.Immediate8)
                    return Unsupported("AVX extract128 操作数未支持");
                Value half = b.Extract(ReadVector(1), (instruction.Immediate8 & 1) * 128, 128);
                if (IsVector(0)) WriteVector(0, half); else b.Store(Address(), half);
            }
            return Next();
        }
    }
}
