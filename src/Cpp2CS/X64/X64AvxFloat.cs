using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private LiftResult AvxRound()
        {
            bool scalar = VectorName is "roundss" or "roundsd";
            int width = VectorName.EndsWith('d') ? 64 : 32, sourceOperand = scalar ? 2 : 1;
            if (instruction.OpCount != (scalar ? 4 : 3) || !IsVector(0) || scalar && (!IsVector(0, 128) || !IsVector(1, 128)) ||
                !(scalar ? IsSimdSource(sourceOperand, width) : IsVectorSource(sourceOperand, Width(0))) ||
                instruction.GetOpKind(sourceOperand + 1) != OpKind.Immediate8)
                return Unsupported("AVX ROUND 操作数未支持");
            int immediate = instruction.Immediate8;
            FloatRounding rounding = (immediate & 4) != 0 ? FloatRounding.Current : (immediate & 3) switch
            { 0 => FloatRounding.TiesEven, 1 => FloatRounding.MinusInfinity, 2 => FloatRounding.PlusInfinity, _ => FloatRounding.TowardZero };
            FloatKind kind = (immediate & 8) != 0 ? FloatKind.RoundIntegral : FloatKind.RoundIntegralExact;
            Value source = VectorSource(sourceOperand, scalar ? width : Width(0)), control = b.Read("mxcsr", 32);
            Value flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < source.Width; offset += width)
            {
                var lane = FloatLane(kind, b.Extract(source, offset, width), b.Const(width, 0), width, control, rounding);
                lanes.Add(lane.Data);
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteVector(0, scalar ? b.Concat(b.Extract(ReadVector(1), width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult AvxFused()
        {
            string name = VectorName, order = name[^5..^2];
            FloatKind? kind = name[..^5] switch { "fmadd" => FloatKind.MulAdd, "fmsub" => FloatKind.MulSub,
                "fnmadd" => FloatKind.NegMulAdd, "fnmsub" => FloatKind.NegMulSub, _ => null };
            bool scalar = name.EndsWith("ss", StringComparison.Ordinal) || name.EndsWith("sd", StringComparison.Ordinal);
            int width = name.EndsWith('d') ? 64 : 32;
            if (kind is null || order is not ("132" or "213" or "231") || instruction.OpCount != 3 || !IsVector(0) ||
                scalar && !IsVector(0, 128) || !IsVector(1, Width(0)) || !(scalar ? IsSimdSource(2, width) : IsVectorSource(2, Width(0))))
                return Unsupported("FMA 操作数或运算形式未支持");
            Value destination = ReadVector(0), source2 = ReadVector(1), source3 = VectorSource(2, scalar ? width : Width(0));
            Value control = b.Read("mxcsr", 32), flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < (scalar ? width : Width(0)); offset += width)
            {
                Value d = b.Extract(destination, offset, width), s2 = b.Extract(source2, offset, width), s3 = b.Extract(source3, offset, width);
                (Value a, Value c, Value addend) = order switch { "132" => (d, s3, s2), "213" => (s2, d, s3), _ => (s2, s3, d) };
                Value packed = b.FusedFloat(new(kind.Value, width, width), a, c, addend, control);
                lanes.Add(b.Extract(packed, 0, width));
                flags = b.Or(flags, b.Extract(packed, width, 6));
                traps = b.Or(traps, b.Extract(packed, width + 6, 6));
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteVector(0, scalar ? b.Concat(b.Extract(destination, width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult AvxFloatArithmetic()
        {
            string name = VectorName;
            bool scalar = name.EndsWith("ss", StringComparison.Ordinal) || name.EndsWith("sd", StringComparison.Ordinal);
            bool sqrt = name.StartsWith("sqrt", StringComparison.Ordinal), unary = sqrt && !scalar;
            int width = name.EndsWith('d') ? 64 : 32, sourceOperand = unary ? 1 : 2;
            if (instruction.OpCount != (unary ? 2 : 3) || !IsVector(0) || scalar && !IsVector(0, 128) ||
                !unary && !IsVector(1, Width(0)) || !(scalar ? IsSimdSource(sourceOperand, width) : IsVectorSource(sourceOperand, Width(0))))
                return Unsupported("AVX 浮点操作数不匹配");
            FloatKind kind = name[..^2] switch { "add" => FloatKind.Add, "sub" => FloatKind.Sub, "mul" => FloatKind.Mul,
                "div" => FloatKind.Div, "sqrt" => FloatKind.Sqrt, "min" => FloatKind.Min, _ => FloatKind.Max };
            Value right = VectorSource(sourceOperand, scalar ? width : Width(0)), left = unary ? right : ReadVector(1);
            Value control = b.Read("mxcsr", 32), flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < (scalar ? width : Width(0)); offset += width)
            {
                Value a = b.Extract(left, offset, width), c = b.Extract(right, offset, width);
                var lane = FloatLane(kind, sqrt ? c : a, sqrt ? b.Const(width, 0) : c, width, control);
                lanes.Add(lane.Data);
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteVector(0, scalar ? b.Concat(b.Extract(left, width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult AvxFloatFlags()
        {
            int width = VectorName.EndsWith('d') ? 64 : 32;
            if (instruction.OpCount != 2 || !IsVector(0, 128) || !IsSimdSource(1, width)) return Unsupported("AVX COMIS 操作数不匹配");
            Value control = b.Read("mxcsr", 32);
            var lane = FloatLane(VectorName.StartsWith('u') ? FloatKind.Compare : FloatKind.CompareSignal,
                b.Trunc(ReadVector(0), width), VectorSource(1, width), 4, control);
            FloatStatus(control, lane.Flags, lane.Traps);
            Value unordered = b.Extract(lane.Data, 0, 1);
            b.Write("cf", b.Or(b.Extract(lane.Data, 3, 1), unordered));
            b.Write("zf", b.Or(b.Extract(lane.Data, 2, 1), unordered));
            b.Write("pf", unordered);
            foreach (string flag in new[] { "of", "sf", "af" }) b.Write(flag, b.Const(1, 0));
            return Next();
        }

        private LiftResult AvxFloatMask()
        {
            bool scalar = VectorName is "cmpss" or "cmpsd";
            int width = VectorName.EndsWith('d') ? 64 : 32;
            if (instruction.OpCount != 4 || !IsVector(0) || scalar && !IsVector(0, 128) || !IsVector(1, Width(0)) ||
                !(scalar ? IsSimdSource(2, width) : IsVectorSource(2, Width(0))) || instruction.Op3Kind != OpKind.Immediate8)
                return Unsupported("AVX 浮点掩码比较操作数不匹配");
            int predicate = instruction.Immediate8 & 31;
            bool signaling = predicate is 1 or 2 or 5 or 6 or 9 or 10 or 13 or 14 or 16 or 19 or 20 or 23 or 24 or 27 or 28 or 31;
            Value left = ReadVector(1), right = VectorSource(2, scalar ? width : Width(0));
            Value control = b.Read("mxcsr", 32), flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int offset = 0; offset < (scalar ? width : Width(0)); offset += width)
            {
                var lane = FloatLane(signaling ? FloatKind.CompareSignal : FloatKind.Compare,
                    b.Extract(left, offset, width), b.Extract(right, offset, width), 4, control);
                Value less = b.Extract(lane.Data, 3, 1), equal = b.Extract(lane.Data, 2, 1), unordered = b.Extract(lane.Data, 0, 1);
                Value ordered = b.BoolNot(unordered), lessEqual = b.Or(less, equal);
                Value condition = (predicate & 15) switch
                {
                    0 => equal, 1 => less, 2 => lessEqual, 3 => unordered,
                    4 => b.BoolNot(equal), 5 => b.BoolNot(less), 6 => b.BoolNot(lessEqual), 7 => ordered,
                    8 => b.Or(equal, unordered), 9 => b.Or(less, unordered), 10 => b.Or(lessEqual, unordered), 11 => b.Const(1, 0),
                    12 => b.And(b.BoolNot(equal), ordered), 13 => b.And(b.BoolNot(less), ordered),
                    14 => b.And(b.BoolNot(lessEqual), ordered), _ => b.Const(1, 1)
                };
                lanes.Add(b.Sext(condition, width));
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            Value result = PackLanes(lanes);
            WriteVector(0, scalar ? b.Concat(b.Extract(left, width, 128 - width), result) : result);
            return Next();
        }

        private LiftResult AvxFloatScalarConvert()
        {
            string name = VectorName;
            bool fromInteger = name is "cvtsi2ss" or "cvtsi2sd", toInteger = name.EndsWith("2si", StringComparison.Ordinal);
            int sourceOperand = toInteger ? 1 : 2;
            if (instruction.OpCount != (toInteger ? 2 : 3) ||
                (toInteger ? instruction.Op0Kind != OpKind.Register || !instruction.Op0Register.IsGPR() || Width(0) is not (32 or 64) : !IsVector(0, 128) || !IsVector(1, 128)))
                return Unsupported("AVX 标量转换目的不匹配");
            int inputWidth = fromInteger ? Width(sourceOperand) : name.Contains("ss2", StringComparison.Ordinal) ? 32 : 64;
            int outputWidth = toInteger ? Width(0) : name.EndsWith("ss", StringComparison.Ordinal) ? 32 : 64;
            if (fromInteger ? !IsScalar(sourceOperand, false) || inputWidth is not (32 or 64) : !IsSimdSource(sourceOperand, inputWidth))
                return Unsupported("AVX 标量转换来源不匹配");
            Value source = fromInteger ? ReadOperand(sourceOperand, inputWidth) : VectorSource(sourceOperand, inputWidth), control = b.Read("mxcsr", 32);
            var lane = FloatLane(fromInteger ? FloatKind.FromSigned : toInteger ? FloatKind.ToSigned : FloatKind.Convert,
                source, b.Const(inputWidth, 0), outputWidth, control, name.StartsWith("cvtt", StringComparison.Ordinal) ? FloatRounding.TowardZero : FloatRounding.Current);
            FloatStatus(control, lane.Flags, lane.Traps);
            if (toInteger) WriteRegister(instruction.Op0Register, lane.Data);
            else WriteVector(0, b.Concat(b.Extract(ReadVector(1), outputWidth, 128 - outputWidth), lane.Data));
            return Next();
        }

        private LiftResult AvxFloatPackedConvert()
        {
            string name = VectorName;
            bool fromInteger = name is "cvtdq2ps" or "cvtdq2pd", toInteger = name.EndsWith("2dq", StringComparison.Ordinal);
            int inputWidth = name.StartsWith("cvtpd", StringComparison.Ordinal) || name.StartsWith("cvttpd", StringComparison.Ordinal) ? 64 : 32;
            int outputWidth = name.EndsWith("2pd", StringComparison.Ordinal) ? 64 : 32;
            if (instruction.OpCount != 2 || !IsVector(0)) return Unsupported("AVX packed 转换目的未支持");
            int count = inputWidth > outputWidth ? Width(1) / inputWidth : Width(0) / outputWidth;
            int memoryWidth = inputWidth * count;
            if (count is not (2 or 4 or 8) || outputWidth * count > Width(0) || !(IsVector(1) && Width(1) >= memoryWidth || IsSimdMemory(1, memoryWidth)))
                return Unsupported("AVX packed 转换来源宽度未支持");
            Value source = VectorSource(1, memoryWidth), control = b.Read("mxcsr", 32), flags = b.Const(6, 0), traps = b.Const(6, 0);
            List<Value> lanes = [];
            for (int index = 0; index < count; index++)
            {
                var lane = FloatLane(fromInteger ? FloatKind.FromSigned : toInteger ? FloatKind.ToSigned : FloatKind.Convert,
                    b.Extract(source, index * inputWidth, inputWidth), b.Const(inputWidth, 0), outputWidth, control,
                    name.StartsWith("cvtt", StringComparison.Ordinal) ? FloatRounding.TowardZero : FloatRounding.Current);
                lanes.Add(lane.Data);
                flags = b.Or(flags, lane.Flags);
                traps = b.Or(traps, lane.Traps);
            }
            FloatStatus(control, flags, traps);
            WriteVector(0, Resize(PackLanes(lanes), Width(0)));
            return Next();
        }

        private LiftResult AvxMxcsr()
        {
            if (instruction.OpCount != 1 || !IsSimdMemory(0, 32)) return Unsupported("VEX MXCSR 搬运需要 m32");
            if (VectorName == "stmxcsr") b.Store(Address(), b.Read("mxcsr", 32));
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
