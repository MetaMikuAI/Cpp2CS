using Cpp2CS.Ir;
using Iced.Intel;

namespace Cpp2CS.X64;

public static partial class X64Lifter
{
    private sealed partial class Lifting
    {
        internal LiftResult Atomic()
        {
            if (instruction.Encoding != EncodingKind.Legacy || instruction.Op0Kind != OpKind.Memory || !ValidAddress())
                return Unsupported("原子操作需要合法的 legacy 内存目的地址");
            if (!instruction.HasLockPrefix && instruction.Mnemonic != Mnemonic.Xchg)
                return Unsupported("仅显式 LOCK 或隐式锁定的内存 XCHG 使用原子规则");
            if (instruction.HasRepPrefix && !instruction.HasXreleasePrefix || instruction.HasRepnePrefix && !instruction.HasXacquirePrefix)
                return Unsupported("非 HLE 的额外前缀未建模");
            // The profile disables HLE; only decoder-recognized hints on legal locked forms are ignored.
            if (instruction.Mnemonic is Mnemonic.Cmpxchg8b or Mnemonic.Cmpxchg16b) return AtomicComparePair();
            if (!IsScalar(0, false)) return Unsupported("原子整数宽度未支持");
            return instruction.Mnemonic switch
            {
                Mnemonic.Add or Mnemonic.Adc or Mnemonic.Sub or Mnemonic.Sbb or Mnemonic.Xadd => AtomicArithmetic(),
                Mnemonic.And or Mnemonic.Or or Mnemonic.Xor => AtomicLogical(),
                Mnemonic.Inc or Mnemonic.Dec or Mnemonic.Neg or Mnemonic.Not => AtomicUnary(),
                Mnemonic.Xchg => AtomicExchange(),
                Mnemonic.Cmpxchg => AtomicCompare(),
                Mnemonic.Bts or Mnemonic.Btr or Mnemonic.Btc => AtomicBit(),
                _ => Unsupported("该指令不具有已建模的锁定语义")
            };
        }

        private Value AtomicAddress(int width)
        {
            Value address = Address();
            AtomicAddressGuard(address, width);
            return address;
        }

        private void AtomicAddressGuard(Value address, int width)
        {
            Value end = b.Add(address, b.Const(64, (ulong)width / 8 - 1));
            Value canonical = b.And(b.Eq(address, b.Sext(b.Trunc(address, 48), 64)), b.Eq(end, b.Sext(b.Trunc(end, 48), 64)));
            b.Guard(b.And(canonical, b.BoolNot(b.Ult(end, address))), "x64 locked memory noncanonical or wrapping access is an unmodeled fault stop");
        }

        private LiftResult AtomicArithmetic()
        {
            if (!BinaryOperands() || instruction.Mnemonic == Mnemonic.Xadd && instruction.Op1Kind != OpKind.Register)
                return Unsupported("LOCK 算术操作数形式未支持");
            int width = Width(0);
            Value source = ReadOperand(1, width);
            bool subtract = instruction.Mnemonic is Mnemonic.Sub or Mnemonic.Sbb;
            Value carry = instruction.Mnemonic is Mnemonic.Adc or Mnemonic.Sbb ? b.Read("cf", 1) : b.Const(1, 0);
            Value operand = b.Add(source, b.Zext(carry, width));
            Value old = b.AtomicRmw(AtomicAddress(width), operand, b.Const(width, 0), subtract ? AtomicKind.Sub : AtomicKind.Add);
            var sum = Arithmetic.AddWithCarry(b, old, subtract ? b.Not(source) : source, subtract ? b.BoolNot(carry) : carry);
            if (instruction.Mnemonic == Mnemonic.Xadd) WriteOperand(1, old);
            ArithmeticResult(old, source, sum.Result, sum.Carry, sum.Overflow, subtract);
            return Next();
        }

        private LiftResult AtomicLogical()
        {
            if (!BinaryOperands()) return Unsupported("LOCK 逻辑操作数形式未支持");
            int width = Width(0);
            Value source = ReadOperand(1, width);
            AtomicKind kind = instruction.Mnemonic switch { Mnemonic.And => AtomicKind.And, Mnemonic.Or => AtomicKind.Or, _ => AtomicKind.Xor };
            Value old = b.AtomicRmw(AtomicAddress(width), source, b.Const(width, 0), kind);
            Value result = kind switch { AtomicKind.And => b.And(old, source), AtomicKind.Or => b.Or(old, source), _ => b.Xor(old, source) };
            b.Write("cf", b.Const(1, 0));
            b.Write("of", b.Const(1, 0));
            b.Write("af", b.Undefined(1, "逻辑指令未定义 AF"));
            ResultFlags(result);
            return Next();
        }

        private LiftResult AtomicUnary()
        {
            if (instruction.OpCount != 1) return Unsupported("LOCK 一元操作数形式未支持");
            int width = Width(0);
            AtomicKind kind = instruction.Mnemonic switch { Mnemonic.Inc => AtomicKind.Add, Mnemonic.Dec => AtomicKind.Sub,
                Mnemonic.Neg => AtomicKind.Neg, _ => AtomicKind.Not };
            Value old = b.AtomicRmw(AtomicAddress(width), b.Const(width, 1), b.Const(width, 0), kind);
            if (kind == AtomicKind.Not) return Next();
            bool negate = kind == AtomicKind.Neg, subtract = kind != AtomicKind.Add;
            Value left = negate ? b.Const(width, 0) : old, right = negate ? old : b.Const(width, 1);
            var sum = Arithmetic.AddWithCarry(b, left, subtract ? b.Not(right) : right, b.Const(1, subtract ? 1UL : 0UL));
            ArithmeticResult(left, right, sum.Result, sum.Carry, sum.Overflow, subtract, !negate);
            return Next();
        }

        private LiftResult AtomicExchange()
        {
            if (!BinaryOperands() || instruction.Op1Kind != OpKind.Register) return Unsupported("内存 XCHG 需要同宽通用寄存器来源");
            int width = Width(0);
            Value source = ReadOperand(1, width);
            Value old = b.AtomicRmw(AtomicAddress(width), source, b.Const(width, 0), AtomicKind.Exchange);
            WriteOperand(1, old);
            return Next();
        }

        private LiftResult AtomicCompare()
        {
            if (!BinaryOperands() || instruction.Op1Kind != OpKind.Register) return Unsupported("LOCK CMPXCHG 需要通用寄存器来源");
            int width = Width(0);
            Register accumulator = width switch { 8 => Register.AL, 16 => Register.AX, 32 => Register.EAX, _ => Register.RAX };
            Value full = b.Read("rax", 64), expected = Resize(full, width), source = ReadOperand(1, width);
            Value old = b.AtomicRmw(AtomicAddress(width), source, expected, AtomicKind.CompareExchange);
            var difference = Arithmetic.AddWithCarry(b, expected, b.Not(old), b.Const(1, 1));
            Value equal = b.Eq(expected, old);
            if (width == 32) b.Write("rax", b.Select(equal, full, b.Zext(old, 64)));
            else WriteRegister(accumulator, b.Select(equal, expected, old));
            ArithmeticResult(expected, old, difference.Result, difference.Carry, difference.Overflow, true);
            return Next();
        }

        private LiftResult AtomicComparePair()
        {
            int width = instruction.Mnemonic == Mnemonic.Cmpxchg16b ? 128 : 64, half = width / 2;
            if (instruction.OpCount != 1 || instruction.MemorySize.GetSize() * 8 != width)
                return Unsupported("CMPXCHG8B/16B 需要匹配宽度的内存操作数");
            Value rax = b.Read("rax", 64), rdx = b.Read("rdx", 64);
            Value expected = b.Concat(Resize(rdx, half), Resize(rax, half));
            Value desired = b.Concat(Resize(b.Read("rcx", 64), half), Resize(b.Read("rbx", 64), half));
            Value address = AtomicAddress(width);
            if (width == 128) b.Guard(b.Eq(b.And(address, b.Const(64, 15)), b.Const(64, 0)), "CMPXCHG16B alignment #GP is an unmodeled fault stop");
            Value old = b.AtomicRmw(address, desired, expected, AtomicKind.CompareExchange), equal = b.Eq(old, expected);
            b.Write("rax", b.Select(equal, rax, Resize(b.Extract(old, 0, half), 64)));
            b.Write("rdx", b.Select(equal, rdx, Resize(b.Extract(old, half, half), 64)));
            b.Write("zf", equal);
            return Next();
        }

        private LiftResult AtomicBit()
        {
            if (!BinaryOperands() || Width(0) is not (16 or 32 or 64)) return Unsupported("锁定位操作数形式未支持");
            int width = Width(0);
            Value offset = ReadOperand(1, width), address = Address();
            if (instruction.Op1Kind == OpKind.Register)
            {
                int addressWidth = MemoryAddressWidth(), shift = width == 16 ? 4 : width == 32 ? 5 : 6;
                Value displacement = b.Mul(Resize(b.Sar(offset, b.Const(width, (ulong)shift)), addressWidth, true), b.Const(addressWidth, (ulong)width / 8));
                address = SourceSegment(Resize(b.Add(Resize(Address(false), addressWidth), displacement), 64));
            }
            AtomicAddressGuard(address, width);
            Value index = b.And(offset, b.Const(width, (ulong)width - 1)), mask = b.Shl(b.Const(width, 1), index);
            AtomicKind kind = instruction.Mnemonic switch { Mnemonic.Bts => AtomicKind.Or, Mnemonic.Btr => AtomicKind.And, _ => AtomicKind.Xor };
            Value old = b.AtomicRmw(address, kind == AtomicKind.And ? b.Not(mask) : mask, b.Const(width, 0), kind);
            b.Write("cf", b.Extract(b.Shr(old, index), 0, 1));
            foreach (string flag in new[] { "of", "sf", "af", "pf" }) b.Write(flag, b.Undefined(1, "位测试未定义 " + flag));
            return Next();
        }
    }
}
