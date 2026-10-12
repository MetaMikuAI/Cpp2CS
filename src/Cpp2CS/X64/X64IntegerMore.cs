using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        private LiftResult Divide()
        {
            if (instruction.OpCount != 1 || !IsScalar(0, false)) return Unsupported("除法操作数形式未支持");
            int width = Width(0);
            bool signed = instruction.Mnemonic == Mnemonic.Idiv;
            Register low = width switch { 8 => Register.AL, 16 => Register.AX, 32 => Register.EAX, _ => Register.RAX };
            Register high = width switch { 8 => Register.AH, 16 => Register.DX, 32 => Register.EDX, _ => Register.RDX };
            Value divisor = ReadOperand(0, width);
            Value dividend = width == 8 ? ReadRegister(Register.AX) : b.Concat(ReadRegister(high), ReadRegister(low));
            b.Guard(b.BoolNot(b.Eq(divisor, b.Const(width, 0))), "x64 divide by zero #DE is an unmodeled fault stop");
            Value extended = Resize(divisor, width * 2, signed);
            Value quotient = signed ? b.SDiv(dividend, extended) : b.UDiv(dividend, extended);
            Value narrowed = b.Trunc(quotient, width);
            b.Guard(b.Eq(quotient, Resize(narrowed, width * 2, signed)), "x64 quotient overflow #DE is an unmodeled fault stop");
            Value remainder = b.Trunc(b.Sub(dividend, b.Mul(quotient, extended)), width);
            if (width == 8) WriteRegister(Register.AX, b.Concat(remainder, narrowed));
            else
            {
                WriteRegister(low, narrowed);
                WriteRegister(high, remainder);
            }
            foreach (string flag in ArithmeticFlags) b.Write(flag, b.Undefined(1, "DIV/IDIV undefined " + flag));
            return Next();
        }

        private LiftResult ByteFlags()
        {
            string[] names = ["cf", "pf", "af", "zf", "sf"];
            int[] offsets = [0, 2, 4, 6, 7];
            if (instruction.Mnemonic == Mnemonic.Lahf)
            {
                Value result = b.Const(8, 2);
                for (int index = 0; index < names.Length; index++)
                    result = b.Or(result, b.Shl(b.Zext(b.Read(names[index], 1), 8), b.Const(8, (ulong)offsets[index])));
                WriteRegister(Register.AH, result);
            }
            else
            {
                Value value = ReadRegister(Register.AH);
                for (int index = 0; index < names.Length; index++) b.Write(names[index], b.Extract(value, offsets[index], 1));
            }
            return Next();
        }

        private LiftResult LoopBranch()
        {
            if (instruction.Op0Kind != OpKind.NearBranch64) return Unsupported("LOOP 仅支持近 x64 分支");
            // 解码形式确定地址大小；LOOP 的操作数大小前缀不改变计数寄存器。
            bool narrow = instruction.Code is Code.Loop_rel8_64_ECX or Code.Loope_rel8_64_ECX or Code.Loopne_rel8_64_ECX;
            Register register = narrow ? Register.ECX : Register.RCX;
            Value old = ReadRegister(register), next = b.Sub(old, b.Const(old.Width, 1));
            Value condition = b.BoolNot(b.Eq(next, b.Const(next.Width, 0)));
            if (instruction.Mnemonic != Mnemonic.Loop)
                condition = b.And(condition, instruction.Mnemonic == Mnemonic.Loope ? b.Read("zf", 1) : b.BoolNot(b.Read("zf", 1)));
            CheckStaticTargets(condition);
            WriteRegister(register, next);
            return LiftResult.Supported(b.Finish(MirExit.Branch(condition, b.Const(64, instruction.NearBranchTarget), b.Const(64, instruction.NextIP))));
        }

        private LiftResult CountTrailingZeros()
        {
            if (!BinaryOperands() || instruction.Op0Kind != OpKind.Register || Width(0) is not (16 or 32 or 64))
                return Unsupported("TZCNT 需要 r16/r32/r64 与同宽来源；profile 要求 BMI1");
            int width = Width(0);
            Value source = ReadOperand(1, width), result = b.Const(width, (ulong)width);
            for (int bit = width - 1; bit >= 0; bit--)
                result = b.Select(b.Extract(source, bit, 1), b.Const(width, (ulong)bit), result);
            WriteOperand(0, result);
            b.Write("cf", b.Eq(source, b.Const(width, 0)));
            b.Write("zf", b.Eq(result, b.Const(width, 0)));
            foreach (string flag in new[] { "of", "sf", "af", "pf" }) b.Write(flag, b.Undefined(1, "TZCNT undefined " + flag));
            return Next();
        }

        private LiftResult RotateCarry()
        {
            if (!BinaryOperands()) return Unsupported("RCL/RCR 操作数形式未支持");
            int width = Width(0);
            Value source = ReadOperand(0, width), oldCf = b.Read("cf", 1), oldOf = b.Read("of", 1);
            Value masked = b.And(ReadOperand(1, 8), b.Const(8, width == 64 ? 63UL : 31UL));
            Value count = width is 8 or 16
                ? b.Sub(masked, b.Mul(b.UDiv(masked, b.Const(8, (ulong)width + 1)), b.Const(8, (ulong)width + 1))) : masked;
            Value zero = b.Eq(masked, b.Const(8, 0));
            if (width is 8 or 16)
                b.Guard(b.Or(zero, b.BoolNot(b.Eq(count, b.Const(8, 0)))), "RCL/RCR nonzero masked count reduced to zero needs a resolved OF contract");
            Value combined = b.Concat(oldCf, source), inverse = b.Sub(b.Const(8, (ulong)width + 1), count);
            bool left = instruction.Mnemonic == Mnemonic.Rcl;
            Value rotated = left ? b.Or(b.Shl(combined, count), b.Shr(combined, inverse))
                : b.Or(b.Shr(combined, count), b.Shl(combined, inverse));
            Value result = b.Trunc(rotated, width), carry = b.Extract(rotated, width, 1);
            Value overflow = left ? b.Xor(b.Extract(result, width - 1, 1), carry) : b.Xor(b.Extract(source, width - 1, 1), oldCf);
            WriteOperand(0, result);
            b.Write("cf", carry);
            b.Write("of", b.Select(zero, oldOf, b.Select(b.Eq(masked, b.Const(8, 1)), overflow, b.Undefined(1, "RCL/RCR multiple-bit OF is undefined"))));
            return Next();
        }

        private LiftResult Leave()
        {
            int width = instruction.Code == Code.Leavew ? 16 : 64;
            Value frame = b.Read("rbp", 64), value = b.Load(frame, width);
            WriteRegister(width == 16 ? Register.BP : Register.RBP, value);
            b.Write("rsp", b.Add(frame, b.Const(64, (ulong)width / 8)));
            return Next();
        }

        private Value SourceSegment(Value address) => instruction.MemorySegment switch
        {
            Register.FS => b.Add(address, b.Read("fsbase", 64)),
            Register.GS => b.Add(address, b.Read("gsbase", 64)),
            _ => address
        };

        private LiftResult TranslateByte()
        {
            Register register = instruction.MemoryBase;
            if (register is not (Register.RBX or Register.EBX)) return Unsupported("XLAT 需要 RBX/EBX 基址");
            Value address = ReadRegister(register);
            address = b.Add(address, b.Zext(ReadRegister(Register.AL), address.Width));
            WriteRegister(Register.AL, b.Load(SourceSegment(Resize(address, 64)), 8));
            return Next();
        }

        private static bool IsStringMemory(OpKind kind) => kind is OpKind.MemorySegESI or OpKind.MemorySegRSI
            or OpKind.MemoryESEDI or OpKind.MemoryESRDI;

        private LiftResult StringInstruction()
        {
            bool move = instruction.Mnemonic is Mnemonic.Movsb or Mnemonic.Movsw or Mnemonic.Movsd or Mnemonic.Movsq;
            bool store = instruction.Mnemonic is Mnemonic.Stosb or Mnemonic.Stosw or Mnemonic.Stosd or Mnemonic.Stosq;
            bool load = instruction.Mnemonic is Mnemonic.Lodsb or Mnemonic.Lodsw or Mnemonic.Lodsd or Mnemonic.Lodsq;
            bool compare = instruction.Mnemonic is Mnemonic.Cmpsb or Mnemonic.Cmpsw or Mnemonic.Cmpsd or Mnemonic.Cmpsq;
            bool scan = instruction.Mnemonic is Mnemonic.Scasb or Mnemonic.Scasw or Mnemonic.Scasd or Mnemonic.Scasq;
            if (!(move || store || load || compare || scan)) return Unsupported("字符串 I/O 与重复执行尚未建模");
            int width = instruction.MemorySize.GetSize() * 8;
            if (width is not (8 or 16 or 32 or 64)) return Unsupported("字符串元素宽度未支持");
            bool narrow = instruction.Op0Kind is OpKind.MemorySegESI or OpKind.MemoryESEDI ||
                instruction.Op1Kind is OpKind.MemorySegESI or OpKind.MemoryESEDI;
            int addressWidth = narrow ? 32 : 64;
            Register si = narrow ? Register.ESI : Register.RSI, di = narrow ? Register.EDI : Register.RDI;
            Register accumulator = width switch { 8 => Register.AL, 16 => Register.AX, 32 => Register.EAX, _ => Register.RAX };
            Value destination = compare || scan ? b.Load(Resize(ReadRegister(di), 64), width) : default;
            Value source = move || load || compare ? b.Load(SourceSegment(Resize(ReadRegister(si), 64)), width) : ReadRegister(accumulator);
            if (compare) b.MarkNormalPathOnly("CMPS ordinary reads are serialized destination then source; fault priority and device-memory ordering are unmodeled");
            if (move || store) b.Store(Resize(ReadRegister(di), 64), source);
            if (load) WriteRegister(accumulator, source);
            Value step = b.Const(addressWidth, (ulong)width / 8), df = b.Read("df", 1);
            Value delta = b.Select(df, b.Sub(b.Const(addressWidth, 0), step), step);
            if (move || load || compare) WriteRegister(si, b.Add(ReadRegister(si), delta));
            if (move || store || compare || scan) WriteRegister(di, b.Add(ReadRegister(di), delta));
            if (compare || scan)
            {
                var difference = Arithmetic.AddWithCarry(b, source, b.Not(destination), b.Const(1, 1));
                ArithmeticResult(source, destination, difference.Result, difference.Carry, difference.Overflow, true);
            }
            return Next();
        }
    }
}
