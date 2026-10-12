using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private (Value Data, Value Flags, Value Traps) FloatLane(FloatKind kind, Value a, Value c, int resultWidth,
            Value control, FloatRounding rounding = FloatRounding.Current)
        {
            Value packed = b.Float(new(kind, a.Width, resultWidth, rounding), a, c, control);
            return (b.Trunc(packed, resultWidth), b.Extract(packed, resultWidth, 6), b.Extract(packed, resultWidth + 6, 6));
        }

        private Value MxcsrFlags(Value canonical)
        {
            // 内核 I,Z,O,U,X,D → MXCSR I,D,Z,O,U,X。
            Value result = b.Const(32, 0);
            int[] positions = [0, 2, 3, 4, 5, 1];
            for (int index = 0; index < positions.Length; index++)
                result = b.Or(result, b.Shl(b.Zext(b.Extract(canonical, index, 1), 32), b.Const(32, (ulong)positions[index])));
            return result;
        }

        private void FloatStatus(Value control, Value flags, Value traps)
        {
            Value unmasked = b.And(b.Trunc(MxcsrFlags(traps), 6), b.Not(b.Extract(control, 7, 6)));
            b.Guard(b.Eq(unmasked, b.Const(6, 0)), "unmasked SIMD floating exception state is an unmodeled fault stop");
            b.Write("mxcsr", b.Or(control, MxcsrFlags(flags)));
        }

        private LiftResult FloatArithmetic()
        {
            string name = instruction.Mnemonic.ToString();
            bool scalar = name.EndsWith("ss", StringComparison.OrdinalIgnoreCase) || name.EndsWith("sd", StringComparison.OrdinalIgnoreCase);
            int width = name.EndsWith("sd", StringComparison.OrdinalIgnoreCase) || name.EndsWith("pd", StringComparison.OrdinalIgnoreCase) ? 64 : 32;
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1, scalar ? width : 128))
                return Unsupported("浮点运算仅支持 legacy XMM 与普通来源");
            if (!scalar) SimdAlignment();
            FloatKind kind = instruction.Mnemonic switch
            {
                Mnemonic.Addss or Mnemonic.Addsd or Mnemonic.Addps or Mnemonic.Addpd => FloatKind.Add,
                Mnemonic.Subss or Mnemonic.Subsd or Mnemonic.Subps or Mnemonic.Subpd => FloatKind.Sub,
                Mnemonic.Mulss or Mnemonic.Mulsd or Mnemonic.Mulps or Mnemonic.Mulpd => FloatKind.Mul,
                Mnemonic.Divss or Mnemonic.Divsd or Mnemonic.Divps or Mnemonic.Divpd => FloatKind.Div,
                Mnemonic.Sqrtss or Mnemonic.Sqrtsd or Mnemonic.Sqrtps or Mnemonic.Sqrtpd => FloatKind.Sqrt,
                Mnemonic.Minss or Mnemonic.Minsd or Mnemonic.Minps or Mnemonic.Minpd => FloatKind.Min,
                _ => FloatKind.Max
            };
            Value old = ReadXmm(0), source = ReadSimdSource(1, scalar ? width : 128), control = b.Read("mxcsr", 32);
            Value flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < (scalar ? width : 128); offset += width)
            {
                Value right = b.Extract(source, offset, width);
                var lane = FloatLane(kind, kind == FloatKind.Sqrt ? right : b.Extract(old, offset, width),
                    kind == FloatKind.Sqrt ? b.Const(width, 0) : right, width, control);
                lanes.Add(lane.Data);
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteXmm(0, scalar ? b.Concat(b.Extract(old, width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult FloatFlagsCompare()
        {
            int width = instruction.Mnemonic is Mnemonic.Comisd or Mnemonic.Ucomisd ? 64 : 32;
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1, width))
                return Unsupported("COMIS/UCOMIS 来源形式未支持");
            Value left = b.Trunc(ReadXmm(0), width), right = ReadSimdSource(1, width), control = b.Read("mxcsr", 32);
            var lane = FloatLane(instruction.Mnemonic is Mnemonic.Comiss or Mnemonic.Comisd ? FloatKind.CompareSignal : FloatKind.Compare,
                left, right, 4, control);
            FloatStatus(control, lane.Flags, lane.Traps);
            Value unordered = b.Extract(lane.Data, 0, 1);
            b.Write("cf", b.Or(b.Extract(lane.Data, 3, 1), unordered));
            b.Write("zf", b.Or(b.Extract(lane.Data, 2, 1), unordered));
            b.Write("pf", unordered);
            foreach (string flag in new[] { "of", "sf", "af" }) b.Write(flag, b.Const(1, 0));
            return Next();
        }

        private LiftResult FloatMaskCompare()
        {
            int width = instruction.Mnemonic is Mnemonic.Cmpsd or Mnemonic.Cmppd ? 64 : 32;
            bool scalar = instruction.Mnemonic is Mnemonic.Cmpss or Mnemonic.Cmpsd;
            if (instruction.OpCount != 3 || !IsXmm(0) || !IsSimdSource(1, scalar ? width : 128) || instruction.Op2Kind != OpKind.Immediate8)
                return Unsupported("CMP 浮点掩码比较形式未支持");
            if (!scalar) SimdAlignment();
            int predicate = instruction.Immediate8 & 7;
            Value old = ReadXmm(0), source = ReadSimdSource(1, scalar ? width : 128), control = b.Read("mxcsr", 32);
            Value flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < (scalar ? width : 128); offset += width)
            {
                var lane = FloatLane(predicate is 1 or 2 or 5 or 6 ? FloatKind.CompareSignal : FloatKind.Compare,
                    b.Extract(old, offset, width), b.Extract(source, offset, width), 4, control);
                Value less = b.Extract(lane.Data, 3, 1), equal = b.Extract(lane.Data, 2, 1), unordered = b.Extract(lane.Data, 0, 1);
                Value condition = predicate switch
                {
                    0 => equal, 1 => less, 2 => b.Or(less, equal), 3 => unordered,
                    4 => b.BoolNot(equal), 5 => b.BoolNot(less), 6 => b.BoolNot(b.Or(less, equal)), _ => b.BoolNot(unordered)
                };
                lanes.Add(b.Sext(condition, width));
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteXmm(0, scalar ? b.Concat(b.Extract(old, width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult FloatScalarConvert()
        {
            if (instruction.OpCount != 2) return Unsupported("标量浮点转换操作数数量无效");
            bool fromInteger = instruction.Mnemonic is Mnemonic.Cvtsi2ss or Mnemonic.Cvtsi2sd;
            bool toInteger = instruction.Mnemonic is Mnemonic.Cvtss2si or Mnemonic.Cvtsd2si or Mnemonic.Cvttss2si or Mnemonic.Cvttsd2si;
            int inputWidth, outputWidth;
            Value source;
            if (fromInteger)
            {
                if (!IsXmm(0) || !IsScalar(1, false) || Width(1) is not (32 or 64)) return Unsupported("CVTSI 来源需为 r/m32 或 r/m64");
                inputWidth = Width(1);
                outputWidth = instruction.Mnemonic == Mnemonic.Cvtsi2ss ? 32 : 64;
                source = ReadOperand(1, inputWidth);
            }
            else
            {
                inputWidth = instruction.Mnemonic is Mnemonic.Cvtss2si or Mnemonic.Cvttss2si or Mnemonic.Cvtss2sd ? 32 : 64;
                if (!IsSimdSource(1, inputWidth) || (toInteger ? instruction.Op0Kind != OpKind.Register || !instruction.Op0Register.IsGPR() || Width(0) is not (32 or 64) : !IsXmm(0)))
                    return Unsupported("标量浮点转换来源或目的未支持");
                outputWidth = toInteger ? Width(0) : inputWidth == 32 ? 64 : 32;
                source = ReadSimdSource(1, inputWidth);
            }
            Value control = b.Read("mxcsr", 32);
            var lane = FloatLane(fromInteger ? FloatKind.FromSigned : toInteger ? FloatKind.ToSigned : FloatKind.Convert,
                source, b.Const(inputWidth, 0), outputWidth, control,
                instruction.Mnemonic is Mnemonic.Cvttss2si or Mnemonic.Cvttsd2si ? FloatRounding.TowardZero : FloatRounding.Current);
            FloatStatus(control, lane.Flags, lane.Traps);
            if (toInteger) WriteRegister(instruction.Op0Register, lane.Data);
            else WriteXmm(0, b.Concat(b.Extract(ReadXmm(0), outputWidth, 128 - outputWidth), lane.Data));
            return Next();
        }

        private LiftResult FloatPackedConvert()
        {
            bool fromInteger = instruction.Mnemonic is Mnemonic.Cvtdq2ps or Mnemonic.Cvtdq2pd;
            bool toInteger = instruction.Mnemonic is Mnemonic.Cvtps2dq or Mnemonic.Cvttps2dq or Mnemonic.Cvtpd2dq or Mnemonic.Cvttpd2dq;
            int inputWidth = instruction.Mnemonic is Mnemonic.Cvtpd2ps or Mnemonic.Cvtpd2dq or Mnemonic.Cvttpd2dq ? 64 : 32;
            int outputWidth = instruction.Mnemonic is Mnemonic.Cvtdq2pd or Mnemonic.Cvtps2pd ? 64 : 32;
            int count = 128 / Math.Max(inputWidth, outputWidth), memoryWidth = inputWidth * count;
            if (instruction.OpCount != 2 || !IsXmm(0) || !IsSimdSource(1, memoryWidth)) return Unsupported("packed 浮点转换来源未支持");
            if (memoryWidth == 128) SimdAlignment();
            Value source = ReadSimdSource(1, memoryWidth), control = b.Read("mxcsr", 32);
            Value flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int index = 0; index < count; index++)
            {
                var lane = FloatLane(fromInteger ? FloatKind.FromSigned : toInteger ? FloatKind.ToSigned : FloatKind.Convert,
                    b.Extract(source, index * inputWidth, inputWidth), b.Const(inputWidth, 0), outputWidth, control,
                    instruction.Mnemonic is Mnemonic.Cvttps2dq or Mnemonic.Cvttpd2dq ? FloatRounding.TowardZero : FloatRounding.Current);
                lanes.Add(lane.Data);
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            WriteXmm(0, Resize(PackLanes(lanes), 128));
            return Next();
        }

        private LiftResult MoveMxcsr()
        {
            if (instruction.OpCount != 1 || !IsSimdMemory(0, 32)) return Unsupported("MXCSR 搬运需要 m32");
            if (instruction.Mnemonic == Mnemonic.Stmxcsr) b.Store(Address(), b.Read("mxcsr", 32));
            else
            {
                Value value = b.Load(Address(), 32);
                b.Guard(b.Eq(b.Extract(value, 16, 16), b.Const(16, 0)), "reserved MXCSR bits #GP is an unmodeled fault stop");
                b.Write("mxcsr", value);
            }
            return Next();
        }
    }
}
