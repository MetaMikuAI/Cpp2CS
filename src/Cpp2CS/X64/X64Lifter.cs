using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

/// <summary>在 64 位、CET 关闭的映像地址配置下提升整数及 legacy SSE 指令。</summary>
public static partial class X64Lifter
{
    public static LiftResult Lift(InstructionOrigin origin, in Instruction instruction)
    {
        if (instruction.IP != origin.Address || instruction.Length != origin.Bytes.Length)
            return LiftResult.Unsupported(instruction.Code.ToString(), "解码地址或长度与原始字节不一致");
        if (instruction.IsInvalid || instruction.CodeSize != CodeSize.Code64)
            return LiftResult.Unsupported(instruction.Code.ToString(), "不是有效的 x64 指令");
        if (instruction.Encoding != EncodingKind.Legacy)
            return LiftResult.Unsupported(instruction.Code.ToString(), "仅支持 legacy 编码，VEX/EVEX 等状态尚未建模");
        if (instruction.HasLockPrefix || instruction.HasXacquirePrefix || instruction.HasXreleasePrefix)
            return LiftResult.Unsupported(instruction.Code.ToString(), "原子性与事务前缀尚未建模");
        if (instruction.HasRepPrefix || instruction.HasRepnePrefix)
            return LiftResult.Unsupported(instruction.Code.ToString(), "重复或额外前缀尚未建模");
        if (instruction.IsPrivileged)
            return LiftResult.Unsupported(instruction.Code.ToString(), "特权环境尚未建模");
        return new Lifting(origin, instruction).Run();
    }

    private sealed partial class Lifting
    {
        private static readonly string[] ArithmeticFlags = ["cf", "pf", "af", "zf", "sf", "of"];
        private readonly Instruction instruction;
        private readonly MirBuilder b;
        private readonly string form;

        internal Lifting(InstructionOrigin origin, Instruction instruction)
        {
            this.instruction = instruction;
            form = instruction.Code.ToString();
            b = new MirBuilder(Architecture.X64, origin, "x64." + form);
        }

        internal LiftResult Run()
        {
            string name = instruction.Mnemonic.ToString();
            if (instruction.ConditionCode != ConditionCode.None)
            {
                if (instruction.IsJccShortOrNear)
                    return ConditionalBranch();
                if (name.StartsWith("Cmov", StringComparison.Ordinal))
                    return ConditionalMove();
                if (name.StartsWith("Set", StringComparison.Ordinal))
                    return SetCondition();
            }
            if (IsStringMemory(instruction.Op0Kind) || IsStringMemory(instruction.Op1Kind))
                return StringInstruction();

            return instruction.Mnemonic switch
            {
                Mnemonic.Nop => Next(),
                Mnemonic.Mov => Move(),
                Mnemonic.Movss or Mnemonic.Movsd => ScalarSimdMove(),
                Mnemonic.Movaps or Mnemonic.Movups or Mnemonic.Movapd or Mnemonic.Movupd
                    or Mnemonic.Movdqa or Mnemonic.Movdqu => PackedMove(),
                Mnemonic.Movd or Mnemonic.Movq => IntegerSimdMove(),
                Mnemonic.Movlps or Mnemonic.Movhps or Mnemonic.Movlpd or Mnemonic.Movhpd
                    or Mnemonic.Movhlps or Mnemonic.Movlhps => HalfSimdMove(),
                Mnemonic.Andps or Mnemonic.Andpd or Mnemonic.Andnps or Mnemonic.Andnpd
                    or Mnemonic.Orps or Mnemonic.Orpd or Mnemonic.Xorps or Mnemonic.Xorpd
                    or Mnemonic.Pand or Mnemonic.Pandn or Mnemonic.Por or Mnemonic.Pxor => PackedLogical(),
                Mnemonic.Shufps or Mnemonic.Shufpd or Mnemonic.Pshufd or Mnemonic.Pshuflw or Mnemonic.Pshufhw => PackedShuffle(),
                Mnemonic.Unpcklps or Mnemonic.Unpckhps or Mnemonic.Unpcklpd or Mnemonic.Unpckhpd
                    or Mnemonic.Punpcklbw or Mnemonic.Punpckhbw or Mnemonic.Punpcklwd or Mnemonic.Punpckhwd
                    or Mnemonic.Punpckldq or Mnemonic.Punpckhdq or Mnemonic.Punpcklqdq or Mnemonic.Punpckhqdq => PackedUnpack(),
                Mnemonic.Psrldq or Mnemonic.Pslldq => PackedByteShift(),
                Mnemonic.Movmskps or Mnemonic.Movmskpd or Mnemonic.Pmovmskb => PackedMask(),
                Mnemonic.Pextrw => ExtractWord(),
                Mnemonic.Paddb or Mnemonic.Paddw or Mnemonic.Paddd or Mnemonic.Paddq
                    or Mnemonic.Psubb or Mnemonic.Psubw or Mnemonic.Psubd or Mnemonic.Psubq
                    or Mnemonic.Paddsb or Mnemonic.Paddsw or Mnemonic.Paddusb or Mnemonic.Paddusw
                    or Mnemonic.Psubsb or Mnemonic.Psubsw or Mnemonic.Psubusb or Mnemonic.Psubusw
                    or Mnemonic.Pcmpeqb or Mnemonic.Pcmpeqw or Mnemonic.Pcmpeqd or Mnemonic.Pcmpeqq
                    or Mnemonic.Pcmpgtb or Mnemonic.Pcmpgtw or Mnemonic.Pcmpgtd
                    or Mnemonic.Pminub or Mnemonic.Pmaxub or Mnemonic.Pminsw or Mnemonic.Pmaxsw
                    or Mnemonic.Pminsb or Mnemonic.Pmaxsb or Mnemonic.Pminuw or Mnemonic.Pmaxuw
                    or Mnemonic.Pminsd or Mnemonic.Pmaxsd or Mnemonic.Pminud or Mnemonic.Pmaxud
                    or Mnemonic.Pmullw or Mnemonic.Pmulhw or Mnemonic.Pmulhuw or Mnemonic.Pmulld => PackedInteger(),
                Mnemonic.Pshufb => PackedShuffleBytes(),
                Mnemonic.Pmovsxbw or Mnemonic.Pmovsxbd or Mnemonic.Pmovsxbq or Mnemonic.Pmovsxwd or Mnemonic.Pmovsxwq or Mnemonic.Pmovsxdq
                    or Mnemonic.Pmovzxbw or Mnemonic.Pmovzxbd or Mnemonic.Pmovzxbq or Mnemonic.Pmovzxwd or Mnemonic.Pmovzxwq or Mnemonic.Pmovzxdq => PackedExtend(),
                Mnemonic.Ptest => PackedTest(),
                Mnemonic.Psllw or Mnemonic.Pslld or Mnemonic.Psllq or Mnemonic.Psrlw or Mnemonic.Psrld or Mnemonic.Psrlq
                    or Mnemonic.Psraw or Mnemonic.Psrad => PackedLaneShift(),
                Mnemonic.Addss or Mnemonic.Addsd or Mnemonic.Addps or Mnemonic.Addpd
                    or Mnemonic.Subss or Mnemonic.Subsd or Mnemonic.Subps or Mnemonic.Subpd
                    or Mnemonic.Mulss or Mnemonic.Mulsd or Mnemonic.Mulps or Mnemonic.Mulpd
                    or Mnemonic.Divss or Mnemonic.Divsd or Mnemonic.Divps or Mnemonic.Divpd
                    or Mnemonic.Sqrtss or Mnemonic.Sqrtsd or Mnemonic.Sqrtps or Mnemonic.Sqrtpd
                    or Mnemonic.Minss or Mnemonic.Minsd or Mnemonic.Minps or Mnemonic.Minpd
                    or Mnemonic.Maxss or Mnemonic.Maxsd or Mnemonic.Maxps or Mnemonic.Maxpd => FloatArithmetic(),
                Mnemonic.Comiss or Mnemonic.Comisd or Mnemonic.Ucomiss or Mnemonic.Ucomisd => FloatFlagsCompare(),
                Mnemonic.Cmpss or Mnemonic.Cmpsd or Mnemonic.Cmpps or Mnemonic.Cmppd => FloatMaskCompare(),
                Mnemonic.Cvtsi2ss or Mnemonic.Cvtsi2sd or Mnemonic.Cvtss2si or Mnemonic.Cvtsd2si
                    or Mnemonic.Cvttss2si or Mnemonic.Cvttsd2si or Mnemonic.Cvtss2sd or Mnemonic.Cvtsd2ss => FloatScalarConvert(),
                Mnemonic.Cvtdq2ps or Mnemonic.Cvtdq2pd or Mnemonic.Cvtps2pd or Mnemonic.Cvtpd2ps
                    or Mnemonic.Cvtps2dq or Mnemonic.Cvttps2dq or Mnemonic.Cvtpd2dq or Mnemonic.Cvttpd2dq => FloatPackedConvert(),
                Mnemonic.Ldmxcsr or Mnemonic.Stmxcsr => MoveMxcsr(),
                Mnemonic.Movzx => ExtendMove(false),
                Mnemonic.Movsx or Mnemonic.Movsxd => ExtendMove(true),
                Mnemonic.Lea => Lea(),
                Mnemonic.Add or Mnemonic.Adc or Mnemonic.Sub or Mnemonic.Sbb or Mnemonic.Cmp => ArithmeticBinary(),
                Mnemonic.And or Mnemonic.Or or Mnemonic.Xor or Mnemonic.Test => LogicalBinary(),
                Mnemonic.Inc or Mnemonic.Dec or Mnemonic.Neg or Mnemonic.Not => Unary(),
                Mnemonic.Shl or Mnemonic.Shr or Mnemonic.Sar or Mnemonic.Rol or Mnemonic.Ror => Shift(),
                Mnemonic.Rcl or Mnemonic.Rcr => RotateCarry(),
                Mnemonic.Mul or Mnemonic.Imul => Multiply(),
                Mnemonic.Div or Mnemonic.Idiv => Divide(),
                Mnemonic.Xchg => Exchange(),
                Mnemonic.Bswap => ByteSwap(),
                Mnemonic.Bt or Mnemonic.Bts or Mnemonic.Btr or Mnemonic.Btc => BitTest(),
                Mnemonic.Bsf or Mnemonic.Bsr => BitScan(),
                Mnemonic.Tzcnt => CountTrailingZeros(),
                Mnemonic.Cbw or Mnemonic.Cwde or Mnemonic.Cdqe or Mnemonic.Cwd or Mnemonic.Cdq or Mnemonic.Cqo => ExtendAccumulator(),
                Mnemonic.Clc or Mnemonic.Stc or Mnemonic.Cmc or Mnemonic.Cld or Mnemonic.Std => SimpleFlag(),
                Mnemonic.Lahf or Mnemonic.Sahf => ByteFlags(),
                Mnemonic.Loop or Mnemonic.Loope or Mnemonic.Loopne => LoopBranch(),
                Mnemonic.Jmp => Jump(),
                Mnemonic.Jrcxz or Mnemonic.Jecxz => CountBranch(),
                Mnemonic.Call => Call(),
                Mnemonic.Ret => Return(),
                Mnemonic.Push => Push(),
                Mnemonic.Pop => Pop(),
                Mnemonic.Leave => Leave(),
                Mnemonic.Xlatb => TranslateByte(),
                Mnemonic.Ud2 => LiftResult.Supported(b.Finish(MirExit.Trap("x64.#UD", instruction.IP))),
                Mnemonic.Int3 => LiftResult.Supported(b.Finish(MirExit.Trap("x64.#BP", instruction.NextIP))),
                _ => Unsupported("尚无该指令形式的语义规则")
            };
        }

        private LiftResult Unsupported(string reason) => LiftResult.Unsupported(form, reason);
        private LiftResult Next() => LiftResult.Supported(b.Finish(MirExit.Next(instruction.NextIP)));

        private bool IsScalar(int operand, bool immediate = true)
        {
            if (operand >= instruction.OpCount)
                return false;
            return instruction.GetOpKind(operand) switch
            {
                OpKind.Register => instruction.GetOpRegister(operand).IsGPR(),
                OpKind.Memory => instruction.MemorySize.GetSize() is 1 or 2 or 4 or 8 && ValidAddress(),
                OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64
                    or OpKind.Immediate8to16 or OpKind.Immediate8to32 or OpKind.Immediate8to64
                    or OpKind.Immediate32to64 => immediate,
                _ => false
            };
        }

        private bool ValidAddress() =>
            (instruction.MemoryBase == Register.None || instruction.MemoryBase.IsGPR32() || instruction.MemoryBase.IsGPR64() || instruction.MemoryBase.IsIP()) &&
            (instruction.MemoryIndex == Register.None || instruction.MemoryIndex.IsGPR32() || instruction.MemoryIndex.IsGPR64());

        private bool BinaryOperands() => instruction.OpCount == 2 && IsScalar(0, false) && IsScalar(1);

        private int Width(int operand) => instruction.GetOpKind(operand) == OpKind.Register
            ? instruction.GetOpRegister(operand).GetSize() * 8
            : instruction.MemorySize.GetSize() * 8;

        private Value Resize(Value value, int width, bool signed = false) => value.Width == width ? value
            : value.Width > width ? b.Trunc(value, width)
            : signed ? b.Sext(value, width) : b.Zext(value, width);

        private Value ReadRegister(Register register)
        {
            Value full = b.Read(register.GetFullRegister().ToString().ToLowerInvariant(), 64);
            int width = register.GetSize() * 8;
            return width == 64 ? full : b.Extract(full, HighByte(register) ? 8 : 0, width);
        }

        private void WriteRegister(Register register, Value value)
        {
            string slot = register.GetFullRegister().ToString().ToLowerInvariant();
            int width = register.GetSize() * 8;
            value = Resize(value, width);
            if (width >= 32)
            {
                b.Write(slot, Resize(value, 64));
                return;
            }
            Value old = b.Read(slot, 64);
            int offset = HighByte(register) ? 8 : 0;
            if (offset != 0)
                value = b.Concat(value, b.Extract(old, 0, offset));
            b.Write(slot, b.Concat(b.Extract(old, offset + width, 64 - offset - width), value));
        }

        private static bool HighByte(Register register) => register is Register.AH or Register.BH or Register.CH or Register.DH;

        private int MemoryAddressWidth() => instruction.MemoryBase.IsGPR32() || instruction.MemoryBase == Register.EIP || instruction.MemoryIndex.IsGPR32() ||
            instruction.MemoryBase == Register.None && instruction.MemoryIndex == Register.None && instruction.MemoryDisplSize == 4 ? 32 : 64;

        private Value AddressRegister(Register register, Value? stackOverride) => stackOverride is { } stack && register is Register.RSP or Register.ESP
            ? Resize(stack, register.GetSize() * 8) : ReadRegister(register);

        private Value Address(bool includeSegment = true, Value? stackOverride = null)
        {
            Value address;
            if (instruction.IsIPRelativeMemoryOperand)
            {
                address = b.Const(64, instruction.IPRelativeMemoryAddress);
            }
            else
            {
                int width = MemoryAddressWidth();
                address = b.Const(width, instruction.MemoryDisplacement64);
                if (instruction.MemoryBase != Register.None)
                    address = b.Add(address, Resize(AddressRegister(instruction.MemoryBase, stackOverride), width));
                if (instruction.MemoryIndex != Register.None)
                {
                    Value index = Resize(AddressRegister(instruction.MemoryIndex, stackOverride), width);
                    address = b.Add(address, b.Mul(index, b.Const(width, (ulong)instruction.MemoryIndexScale)));
                }
                address = Resize(address, 64);
            }
            if (includeSegment && instruction.MemorySegment is Register.FS or Register.GS)
                address = b.Add(address, b.Read(instruction.MemorySegment == Register.FS ? "fsbase" : "gsbase", 64));
            return address;
        }

        private Value ReadOperand(int operand, int width)
        {
            return instruction.GetOpKind(operand) switch
            {
                OpKind.Register => Resize(ReadRegister(instruction.GetOpRegister(operand)), width),
                OpKind.Memory => b.Load(Address(), width),
                _ => b.Const(width, instruction.GetImmediate(operand))
            };
        }

        private void WriteOperand(int operand, Value value)
        {
            if (instruction.GetOpKind(operand) == OpKind.Register)
                WriteRegister(instruction.GetOpRegister(operand), value);
            else
                b.Store(Address(), value);
        }

        private LiftResult Move()
        {
            if (!BinaryOperands())
                return Unsupported("MOV 仅支持通用寄存器、普通整数内存与立即数");
            WriteOperand(0, ReadOperand(1, Width(0)));
            return Next();
        }

        private LiftResult ExtendMove(bool signed)
        {
            if (!BinaryOperands() || instruction.Op0Kind != OpKind.Register || !IsScalar(1, false))
                return Unsupported("扩展搬运的操作数形式未支持");
            WriteOperand(0, Resize(ReadOperand(1, Width(1)), Width(0), signed));
            return Next();
        }

        private LiftResult Lea()
        {
            if (instruction.OpCount != 2 || instruction.Op0Kind != OpKind.Register || !instruction.Op0Register.IsGPR() ||
                instruction.Op1Kind != OpKind.Memory || !ValidAddress())
                return Unsupported("LEA 地址形式未支持");
            WriteOperand(0, Resize(Address(false), Width(0)));
            return Next();
        }

        private void ResultFlags(Value result)
        {
            b.Write("sf", b.Extract(result, result.Width - 1, 1));
            b.Write("zf", b.Eq(result, b.Const(result.Width, 0)));
            b.Write("pf", Arithmetic.Parity(b, result));
        }

        private void ArithmeticResult(Value left, Value right, Value result, Value carry, Value overflow, bool subtract, bool preserveCarry = false)
        {
            if (!preserveCarry)
                b.Write("cf", subtract ? b.BoolNot(carry) : carry);
            b.Write("of", overflow);
            b.Write("af", b.Extract(b.Xor(b.Xor(left, right), result), 4, 1));
            ResultFlags(result);
        }

        private LiftResult ArithmeticBinary()
        {
            if (!BinaryOperands())
                return Unsupported("算术操作数形式未支持");
            int width = Width(0);
            Value left = ReadOperand(0, width), right = ReadOperand(1, width);
            bool subtract = instruction.Mnemonic is Mnemonic.Sub or Mnemonic.Sbb or Mnemonic.Cmp;
            Value carry = instruction.Mnemonic switch
            {
                Mnemonic.Adc => b.Read("cf", 1),
                Mnemonic.Sbb => b.BoolNot(b.Read("cf", 1)),
                _ => b.Const(1, subtract ? 1UL : 0UL)
            };
            var sum = Arithmetic.AddWithCarry(b, left, subtract ? b.Not(right) : right, carry);
            if (instruction.Mnemonic != Mnemonic.Cmp)
                WriteOperand(0, sum.Result);
            ArithmeticResult(left, right, sum.Result, sum.Carry, sum.Overflow, subtract);
            return Next();
        }

        private LiftResult LogicalBinary()
        {
            if (!BinaryOperands())
                return Unsupported("逻辑操作数形式未支持");
            int width = Width(0);
            Value left = ReadOperand(0, width), right = ReadOperand(1, width);
            Value result = instruction.Mnemonic switch
            {
                Mnemonic.Or => b.Or(left, right),
                Mnemonic.Xor => b.Xor(left, right),
                _ => b.And(left, right)
            };
            if (instruction.Mnemonic != Mnemonic.Test)
                WriteOperand(0, result);
            b.Write("cf", b.Const(1, 0));
            b.Write("of", b.Const(1, 0));
            b.Write("af", b.Undefined(1, "逻辑指令未定义 AF"));
            ResultFlags(result);
            return Next();
        }

        private LiftResult Unary()
        {
            if (instruction.OpCount != 1 || !IsScalar(0, false))
                return Unsupported("一元操作数形式未支持");
            int width = Width(0);
            Value old = ReadOperand(0, width);
            if (instruction.Mnemonic == Mnemonic.Not)
            {
                WriteOperand(0, b.Not(old));
                return Next();
            }
            bool negate = instruction.Mnemonic == Mnemonic.Neg;
            bool subtract = instruction.Mnemonic != Mnemonic.Inc;
            Value left = negate ? b.Const(width, 0) : old;
            Value right = negate ? old : b.Const(width, 1);
            var sum = Arithmetic.AddWithCarry(b, left, subtract ? b.Not(right) : right, b.Const(1, subtract ? 1UL : 0UL));
            WriteOperand(0, sum.Result);
            ArithmeticResult(left, right, sum.Result, sum.Carry, sum.Overflow, subtract, !negate);
            return Next();
        }

        private LiftResult Shift()
        {
            if (!BinaryOperands())
                return Unsupported("移位操作数形式未支持");
            int width = Width(0);
            Value input = ReadOperand(0, width), raw = ReadOperand(1, width);
            Value count = b.And(raw, b.Const(width, width == 64 ? 63UL : 31UL));
            Value zero = b.Eq(count, b.Const(width, 0)), one = b.Eq(count, b.Const(width, 1));
            bool rotate = instruction.Mnemonic is Mnemonic.Rol or Mnemonic.Ror;
            bool left = instruction.Mnemonic is Mnemonic.Shl or Mnemonic.Rol;
            Value result;
            Value cf;
            if (rotate)
            {
                Value k = b.And(count, b.Const(width, (ulong)width - 1));
                Value back = b.Sub(b.Const(width, (ulong)width), k);
                result = left ? b.Or(b.Shl(input, k), b.Shr(input, back)) : b.Or(b.Shr(input, k), b.Shl(input, back));
                cf = b.Extract(result, left ? 0 : width - 1, 1);
            }
            else
            {
                result = instruction.Mnemonic == Mnemonic.Sar ? b.Sar(input, count)
                    : left ? b.Shl(input, count) : b.Shr(input, count);
                Value shift = left ? b.Sub(b.Const(width, (ulong)width), count) : b.Sub(count, b.Const(width, 1));
                Value last = b.Extract(b.Shr(input, shift), 0, 1);
                Value outside = instruction.Mnemonic == Mnemonic.Sar ? b.Extract(input, width - 1, 1)
                    : b.Undefined(1, "SHL/SHR 计数达到操作数宽度时 CF 未定义");
                cf = b.Select(b.Ult(count, b.Const(width, (ulong)width)), last, outside);
            }
            Value of = instruction.Mnemonic switch
            {
                Mnemonic.Sar => b.Const(1, 0),
                Mnemonic.Shr => b.Extract(input, width - 1, 1),
                Mnemonic.Ror => b.Xor(b.Extract(result, width - 1, 1), b.Extract(result, width - 2, 1)),
                _ => b.Xor(b.Extract(result, width - 1, 1), cf)
            };
            Value oldCf = b.Read("cf", 1), oldOf = b.Read("of", 1);
            Value newOf = b.Select(one, of, b.Undefined(1, "多位移位或旋转未定义 OF"));
            WriteOperand(0, result);
            b.Write("cf", b.Select(zero, oldCf, cf));
            b.Write("of", b.Select(zero, oldOf, newOf));
            if (!rotate)
            {
                b.Write("sf", b.Select(zero, b.Read("sf", 1), b.Extract(result, width - 1, 1)));
                b.Write("zf", b.Select(zero, b.Read("zf", 1), b.Eq(result, b.Const(width, 0))));
                b.Write("pf", b.Select(zero, b.Read("pf", 1), Arithmetic.Parity(b, result)));
                b.Write("af", b.Select(zero, b.Read("af", 1), b.Undefined(1, "非零移位未定义 AF")));
            }
            return Next();
        }

        private LiftResult Multiply()
        {
            if (instruction.OpCount is < 1 or > 3 || !IsScalar(0, false))
                return Unsupported("乘法操作数形式未支持");
            bool implicitAccumulator = instruction.OpCount == 1;
            if (!implicitAccumulator && (instruction.Mnemonic != Mnemonic.Imul || instruction.Op0Kind != OpKind.Register ||
                !IsScalar(1) || (instruction.OpCount == 3 && !IsScalar(2))))
                return Unsupported("乘法操作数形式未支持");
            int width = Width(0);
            Register accumulator = width switch { 8 => Register.AL, 16 => Register.AX, 32 => Register.EAX, _ => Register.RAX };
            Value left = implicitAccumulator ? ReadRegister(accumulator) : ReadOperand(instruction.OpCount == 3 ? 1 : 0, width);
            Value right = ReadOperand(implicitAccumulator ? 0 : instruction.OpCount == 3 ? 2 : 1, width);
            bool signed = instruction.Mnemonic == Mnemonic.Imul;
            Value product = b.Mul(Resize(left, width * 2, signed), Resize(right, width * 2, signed));
            Value low = b.Trunc(product, width), high = b.Extract(product, width, width);
            Value overflow = signed ? b.BoolNot(b.Eq(product, b.Sext(low, width * 2)))
                : b.BoolNot(b.Eq(high, b.Const(width, 0)));
            if (implicitAccumulator)
            {
                if (width == 8)
                    WriteRegister(Register.AX, product);
                else
                {
                    WriteRegister(accumulator, low);
                    WriteRegister(width == 16 ? Register.DX : width == 32 ? Register.EDX : Register.RDX, high);
                }
            }
            else
                WriteOperand(0, low);
            b.Write("cf", overflow);
            b.Write("of", overflow);
            foreach (string flag in new[] { "sf", "zf", "af", "pf" })
                b.Write(flag, b.Undefined(1, "MUL/IMUL 未定义 " + flag));
            return Next();
        }

        private LiftResult Exchange()
        {
            if (!BinaryOperands() || instruction.Op0Kind != OpKind.Register || instruction.Op1Kind != OpKind.Register)
                return Unsupported("内存 XCHG 的原子效应尚未建模");
            Value left = ReadOperand(0, Width(0)), right = ReadOperand(1, Width(1));
            WriteOperand(0, right);
            WriteOperand(1, left);
            return Next();
        }

        private LiftResult ByteSwap()
        {
            if (instruction.OpCount != 1 || instruction.Op0Kind != OpKind.Register || !IsScalar(0, false) || Width(0) is not (32 or 64))
                return Unsupported("BSWAP 只支持 32/64 位通用寄存器");
            Value old = ReadOperand(0, Width(0)), result = b.Extract(old, 0, 8);
            for (int offset = 8; offset < old.Width; offset += 8)
                result = b.Concat(result, b.Extract(old, offset, 8));
            WriteOperand(0, result);
            return Next();
        }

        private LiftResult BitTest()
        {
            if (!BinaryOperands()) return Unsupported("位测试操作数形式未支持");
            int width = Width(0);
            Value offset = ReadOperand(1, width);
            Value address = default;
            if (instruction.Op0Kind == OpKind.Memory)
            {
                address = Address();
                if (instruction.Op1Kind == OpKind.Register)
                {
                    int addressWidth = MemoryAddressWidth(), shift = width == 16 ? 4 : width == 32 ? 5 : 6;
                    Value displacement = b.Mul(Resize(b.Sar(offset, b.Const(width, (ulong)shift)), addressWidth, true), b.Const(addressWidth, (ulong)width / 8));
                    address = SourceSegment(Resize(b.Add(Resize(Address(false), addressWidth), displacement), 64));
                }
            }
            Value old = instruction.Op0Kind == OpKind.Memory ? b.Load(address, width) : ReadOperand(0, width);
            Value index = b.And(offset, b.Const(width, (ulong)width - 1));
            Value bit = b.Extract(b.Shr(old, index), 0, 1);
            if (instruction.Mnemonic != Mnemonic.Bt)
            {
                Value mask = b.Shl(b.Const(width, 1), index);
                Value result = instruction.Mnemonic switch
                {
                    Mnemonic.Bts => b.Or(old, mask),
                    Mnemonic.Btr => b.And(old, b.Not(mask)),
                    _ => b.Xor(old, mask)
                };
                if (instruction.Op0Kind == OpKind.Memory) b.Store(address, result);
                else WriteOperand(0, result);
            }
            b.Write("cf", bit);
            foreach (string flag in new[] { "of", "sf", "af", "pf" })
                b.Write(flag, b.Undefined(1, "位测试未定义 " + flag));
            return Next();
        }

        private LiftResult BitScan()
        {
            if (!BinaryOperands() || instruction.Op0Kind != OpKind.Register || !IsScalar(1, false))
                return Unsupported("位扫描操作数形式未支持");
            int width = Width(0);
            Value source = ReadOperand(1, width), result = b.Const(width, 0);
            if (width == 32)
                b.Guard(b.BoolNot(b.Eq(source, b.Const(width, 0))), "32-bit BSF/BSR zero-source full-register outcome is unmodeled");
            bool forward = instruction.Mnemonic == Mnemonic.Bsf;
            for (int step = 0; step < width; step++)
            {
                int index = forward ? width - 1 - step : step;
                result = b.Select(b.Extract(source, index, 1), b.Const(width, (ulong)index), result);
            }
            Value zero = b.Eq(source, b.Const(width, 0));
            WriteOperand(0, b.Select(zero, b.Undefined(width, "零输入位扫描未定义目的值"), result));
            b.Write("zf", zero);
            foreach (string flag in ArithmeticFlags)
                if (flag != "zf")
                    b.Write(flag, b.Undefined(1, "位扫描未定义 " + flag));
            return Next();
        }

        private LiftResult ExtendAccumulator()
        {
            (Register source, Register target) = instruction.Mnemonic switch
            {
                Mnemonic.Cbw => (Register.AL, Register.AX),
                Mnemonic.Cwde => (Register.AX, Register.EAX),
                Mnemonic.Cdqe => (Register.EAX, Register.RAX),
                Mnemonic.Cwd => (Register.AX, Register.DX),
                Mnemonic.Cdq => (Register.EAX, Register.EDX),
                _ => (Register.RAX, Register.RDX)
            };
            Value value = ReadRegister(source);
            bool highHalf = instruction.Mnemonic is Mnemonic.Cwd or Mnemonic.Cdq or Mnemonic.Cqo;
            WriteRegister(target, highHalf ? b.Sar(value, b.Const(value.Width, (ulong)value.Width - 1))
                : b.Sext(value, target.GetSize() * 8));
            return Next();
        }

        private LiftResult SimpleFlag()
        {
            string slot = instruction.Mnemonic is Mnemonic.Cld or Mnemonic.Std ? "df" : "cf";
            Value value = instruction.Mnemonic == Mnemonic.Cmc ? b.BoolNot(b.Read("cf", 1))
                : b.Const(1, instruction.Mnemonic is Mnemonic.Stc or Mnemonic.Std ? 1UL : 0UL);
            b.Write(slot, value);
            return Next();
        }

        private Value Condition() => instruction.ConditionCode switch
        {
            ConditionCode.o => b.Read("of", 1),
            ConditionCode.no => b.BoolNot(b.Read("of", 1)),
            ConditionCode.b => b.Read("cf", 1),
            ConditionCode.ae => b.BoolNot(b.Read("cf", 1)),
            ConditionCode.e => b.Read("zf", 1),
            ConditionCode.ne => b.BoolNot(b.Read("zf", 1)),
            ConditionCode.be => b.Or(b.Read("cf", 1), b.Read("zf", 1)),
            ConditionCode.a => b.BoolNot(b.Or(b.Read("cf", 1), b.Read("zf", 1))),
            ConditionCode.s => b.Read("sf", 1),
            ConditionCode.ns => b.BoolNot(b.Read("sf", 1)),
            ConditionCode.p => b.Read("pf", 1),
            ConditionCode.np => b.BoolNot(b.Read("pf", 1)),
            ConditionCode.l => b.Xor(b.Read("sf", 1), b.Read("of", 1)),
            ConditionCode.ge => b.BoolNot(b.Xor(b.Read("sf", 1), b.Read("of", 1))),
            ConditionCode.le => b.Or(b.Read("zf", 1), b.Xor(b.Read("sf", 1), b.Read("of", 1))),
            ConditionCode.g => b.BoolNot(b.Or(b.Read("zf", 1), b.Xor(b.Read("sf", 1), b.Read("of", 1)))),
            _ => throw new InvalidOperationException("无条件码的指令不能读取条件")
        };

        private LiftResult ConditionalMove()
        {
            if (!BinaryOperands() || instruction.Op0Kind != OpKind.Register || !IsScalar(1, false))
                return Unsupported("条件搬运操作数形式未支持");
            int width = Width(0);
            Value old = ReadOperand(0, width), source = ReadOperand(1, width), condition = Condition();
            WriteOperand(0, b.Select(condition, source, old));
            return Next();
        }

        private LiftResult SetCondition()
        {
            if (instruction.OpCount != 1 || !IsScalar(0, false) || Width(0) != 8)
                return Unsupported("SETcc 操作数形式未支持");
            WriteOperand(0, b.Zext(Condition(), 8));
            return Next();
        }

        private LiftResult ConditionalBranch()
        {
            if (instruction.Op0Kind != OpKind.NearBranch64)
                return Unsupported("仅支持近 x64 条件转移");
            Value condition = Condition();
            CheckStaticTargets(condition);
            return LiftResult.Supported(b.Finish(MirExit.Branch(condition, b.Const(64, instruction.NearBranchTarget), b.Const(64, instruction.NextIP))));
        }

        private LiftResult CountBranch()
        {
            if (instruction.Op0Kind != OpKind.NearBranch64)
                return Unsupported("计数分支形式未支持");
            Value count = ReadRegister(instruction.Mnemonic == Mnemonic.Jecxz ? Register.ECX : Register.RCX);
            Value condition = b.Eq(count, b.Const(count.Width, 0));
            CheckStaticTargets(condition);
            return LiftResult.Supported(b.Finish(MirExit.Branch(condition,
                b.Const(64, instruction.NearBranchTarget), b.Const(64, instruction.NextIP))));
        }

        private static bool Canonical48(ulong address) => ((long)address << 16 >> 16) == (long)address;

        private void CheckStaticTargets(Value? condition = null)
        {
            if (!Canonical48(instruction.NearBranchTarget))
                b.Guard(condition is { } taken ? b.BoolNot(taken) : b.Const(1, 0), "noncanonical taken target is an unmodeled fault stop; next fetch is excluded");
        }

        private void CheckDynamicTarget(Value target) =>
            b.Guard(b.Eq(target, b.Sext(b.Trunc(target, 48), 64)), "noncanonical indirect target is an unmodeled fault stop; fault priority and delivery are unmodeled");

        private bool IsNearTarget() => instruction.Op0Kind == OpKind.NearBranch64 ||
            (IsScalar(0, false) && Width(0) == 64);

        private Value Target()
        {
            if (instruction.Op0Kind == OpKind.NearBranch64)
            {
                CheckStaticTargets();
                return b.Const(64, instruction.NearBranchTarget);
            }
            Value target = ReadOperand(0, 64);
            CheckDynamicTarget(target);
            return target;
        }

        private LiftResult Jump()
        {
            if (!IsNearTarget())
                return Unsupported("远跳转或非 64 位目标未支持");
            return LiftResult.Supported(b.Finish(MirExit.Jump(Target())));
        }

        private LiftResult Call()
        {
            if (!IsNearTarget())
                return Unsupported("远调用或非 64 位目标未支持");
            Value target = Target();
            Value stack = b.Sub(b.Read("rsp", 64), b.Const(64, 8));
            b.Store(stack, b.Const(64, instruction.NextIP));
            b.Write("rsp", stack);
            b.MarkNormalPathOnly("CALL 栈写入与目标检查的故障顺序未建模；配置要求 CET 关闭");
            return LiftResult.Supported(b.Finish(MirExit.Jump(target)));
        }

        private LiftResult Return()
        {
            if (instruction.Code is not (Code.Retnq or Code.Retnq_imm16))
                return Unsupported("仅支持近 64 位 RET");
            Value stack = b.Read("rsp", 64), target = b.Load(stack, 64);
            CheckDynamicTarget(target);
            ulong adjustment = 8 + (instruction.OpCount == 0 ? 0UL : instruction.GetImmediate(0));
            b.Write("rsp", b.Add(stack, b.Const(64, adjustment)));
            b.MarkNormalPathOnly("RET 目标检查与栈提交的故障顺序未建模；配置要求 CET 关闭");
            return LiftResult.Supported(b.Finish(MirExit.Jump(target)));
        }

        private LiftResult Push()
        {
            int bytes = -instruction.StackPointerIncrement;
            if (instruction.OpCount != 1 || !IsScalar(0) || bytes is not (2 or 8))
                return Unsupported("仅支持普通整数 PUSH");
            Value value = ReadOperand(0, bytes * 8);
            Value stack = b.Sub(b.Read("rsp", 64), b.Const(64, (ulong)bytes));
            b.Store(stack, value);
            b.Write("rsp", stack);
            return Next();
        }

        private LiftResult Pop()
        {
            int bytes = instruction.StackPointerIncrement;
            if (instruction.OpCount != 1 || !IsScalar(0, false) || bytes is not (2 or 8))
                return Unsupported("POP 仅支持通用寄存器或普通 m16/m64");
            Value stack = b.Read("rsp", 64), value = b.Load(stack, bytes * 8);
            Value nextStack = b.Add(stack, b.Const(64, (ulong)bytes));
            if (instruction.Op0Kind == OpKind.Memory)
            {
                b.Store(Address(stackOverride: nextStack), value);
                b.Write("rsp", nextStack);
                b.MarkNormalPathOnly("POP memory uses the incremented stack in destination addressing; fault priority and partial state are unmodeled");
            }
            else
            {
                b.Write("rsp", nextStack);
                WriteOperand(0, value);
            }
            return Next();
        }
    }
}
