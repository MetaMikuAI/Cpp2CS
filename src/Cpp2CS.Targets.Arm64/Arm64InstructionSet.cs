using System.Collections.Immutable;
using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Frontend;
using static Cpp2CS.Native.Terms.CoreOperation;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Targets.Arm64;

/// <summary>小端 A64 编码；解码不保存跨指令状态，未支持的编码一律留下分类原因。</summary>
public sealed partial class Arm64InstructionSet(IImage image) : IInstructionSet
{
    public ImmutableArray<Register> Registers => All;
    public DecodeResult Decode(ulong address)
    {
        if ((address & 3) != 0 || !image.IsExecutable(address, 4))
            return new(null, new("arm64.fetch", "指令地址未对齐或没有四个可执行字节。"));
        return DecodeWord(address, (uint)image.ReadUnsigned(address, 4));
    }
    public static DecodeResult DecodeWord(ulong address, uint word) => new(new(4, e => new Semantics(address, word, e).Run()), null);

    private sealed partial class Semantics(ulong pc, uint word, IEmitter e)
    {
        private int B(int low, int count = 1) => (int)((word >> low) & ((1u << count) - 1));
        private bool Bit(int bit) => B(bit) != 0;
        private bool Is(uint mask, uint value) => (word & mask) == value;
        private int Width => Bit(31) ? 64 : 32;
        private int D => B(0, 5);
        private int A => B(5, 5);
        private int M => B(16, 5);
        private TermTable T => e.Terms;
        private Term K(BigInteger value, int width = 64) => T.Constant(value & ((BigInteger.One << width) - 1), width);
        private Term Op(CoreOperation op, Term a, Term b) => T.Apply(new CoreOperator(op), a.Width, a, b);
        private Term Unary(CoreOperation op, Term a) => T.Apply(new CoreOperator(op), a.Width, a);
        private Term Compare(CoreOperation op, Term a, Term b) => T.Apply(new CoreOperator(op), 1, a, b);
        private Term Choose(Term condition, Term a, Term b) => T.Apply(new CoreOperator(Select), a.Width, condition, a, b);
        private Term Extend(Term a, int width, bool signed = false) => a.Width == width ? a : a.Width > width ? T.Slice(a, 0, width)
            : signed ? T.Apply(new CoreOperator(SignExtend), width, a) : T.Concat(a, K(0, width - a.Width));
        private Term ReadX(int index, int width, bool sp = false) => index == 31 && !sp ? K(0, width) : T.Slice(e.Read(index == 31 ? Sp : X[index]), 0, width);
        private void WriteX(int index, Term value, bool sp = false)
        {
            if (index != 31 || sp) e.Write(index == 31 ? Sp : X[index], Extend(value, 64));
        }
        private void WriteV(int index, Term value) => e.Write(V[index], Extend(value, 128));
        private Term Shift(Term value, int type, Term amount) => Op(type switch { 0 => ShiftLeft, 1 => LogicalShiftRight, 2 => ArithmeticShiftRight, _ => RotateRight }, value, amount);
        private Term Shift(Term value, int type, int amount) => amount == 0 ? value : Shift(value, type, K(amount, value.Width));
        private void Hole(string category = "unallocated")
        {
            var description = category switch
            {
                "floating" => "浮点运算", "vector" => "向量运算", "exclusive" => "独占或有序访问",
                "atomic" => "原子操作", "barrier" => "内存屏障", "system-register" => "系统寄存器",
                "system-trap" => "系统调用陷阱", "branch-extension" => "分支扩展",
                "integer-extension" => "整数扩展", "constrained-unpredictable" => "受约束的不可预测行为",
                _ => "未分配或尚未实现的编码"
            };
            e.Fail(new("arm64." + category, $"{description}：0x{word:x8}"));
        }
        private static long Signed(int value, int bits) => ((long)value << (64 - bits)) >> (64 - bits);
        private ulong Relative(int low, int bits, int scale = 2) => unchecked(pc + (ulong)(Signed(B(low, bits), bits) << scale));
        private Term Condition(int condition)
        {
            var value = (condition >> 1) switch
            {
                0 => e.Read(Z), 1 => e.Read(C), 2 => e.Read(N), 3 => e.Read(Overflow),
                4 => Op(And, e.Read(C), Unary(Not, e.Read(Z))),
                5 => Compare(Equal, e.Read(N), e.Read(Overflow)),
                6 => Op(And, Compare(Equal, e.Read(N), e.Read(Overflow)), Unary(Not, e.Read(Z))),
                _ => K(1, 1)
            };
            return condition < 14 && (condition & 1) != 0 ? Unary(Not, value) : value;
        }
        // AddWithCarry 在一位更宽的无符号数上计算进位；溢出比较输入与结果符号。
        private (Term Result, Term[] Flags) AddCarry(Term a, Term b, Term carry)
        {
            int width = a.Width;
            var full = Op(Add, Op(Add, Extend(a, width + 1), Extend(b, width + 1)), Extend(carry, width + 1));
            var result = T.Slice(full, 0, width);
            var signA = T.Slice(a, width - 1, 1);
            var signB = T.Slice(b, width - 1, 1);
            var signR = T.Slice(result, width - 1, 1);
            return (result, [signR, Compare(Equal, result, K(0, width)), T.Slice(full, width, 1),
                Op(And, Compare(Equal, signA, signB), Compare(NotEqual, signA, signR))]);
        }
        private void Flags(Term[] flags)
        {
            e.Write(N, flags[0]); e.Write(Z, flags[1]); e.Write(C, flags[2]); e.Write(Overflow, flags[3]);
        }
        private Term Arithmetic(Term a, Term b, bool subtract, bool flags, Term? carry = null)
        {
            if (!flags && carry is null) return Op(subtract ? Subtract : Add, a, b);
            var calculated = AddCarry(a, subtract ? Unary(Not, b) : b, carry ?? K(subtract ? 1 : 0, 1));
            if (flags) Flags(calculated.Flags);
            return calculated.Result;
        }
        private Term Logical(Term a, Term b, int opc)
        {
            var result = Op(opc switch { 1 => Or, 2 => Xor, _ => And }, a, b);
            if (opc == 3) Flags([T.Slice(result, result.Width - 1, 1), Compare(Equal, result, K(0, result.Width)), K(0, 1), K(0, 1)]);
            return result;
        }
        public void Run()
        {
            if (Is(0x1f000000, 0x10000000))
            {
                long immediate = Signed((B(5, 19) << 2) | B(29, 2), 21);
                ulong target = Bit(31) ? unchecked((pc & ~4095UL) + (ulong)(immediate << 12)) : unchecked(pc + (ulong)immediate);
                WriteX(D, e.ImageAddress(target)); return;
            }
            if (Is(0x1f800000, 0x11000000))
            {
                WriteX(D, Arithmetic(ReadX(A, Width, true), K((long)B(10, 12) << (Bit(22) ? 12 : 0), Width), Bit(30), Bit(29)), !Bit(29)); return;
            }
            if (Is(0x1f800000, 0x12000000)) { LogicalImmediate(); return; }
            if (Is(0x1f800000, 0x12800000))
            {
                int shift = B(21, 2) * 16, opc = B(29, 2);
                if (shift >= Width || opc == 1) { Hole(); return; }
                var immediate = K((BigInteger)B(5, 16) << shift, Width);
                WriteX(D, opc == 0 ? Unary(Not, immediate) : opc == 2 ? immediate :
                    Op(Or, Op(And, ReadX(D, Width), K(~((BigInteger)65535 << shift), Width)), immediate)); return;
            }
            if (Is(0x1f800000, 0x13000000)) { Bitfield(); return; }
            if (Is(0x1f800000, 0x13800000))
            {
                int shift = B(10, 6);
                if (B(29, 2) != 0 || Bit(21) || Bit(22) != Bit(31) || shift >= Width) { Hole(); return; }
                WriteX(D, T.Slice(T.Concat(ReadX(M, Width), ReadX(A, Width)), shift, Width)); return;
            }
            if (Is(0x1f000000, 0x0a000000))
            {
                if (B(10, 6) >= Width) { Hole(); return; }
                var right = Shift(ReadX(M, Width), B(22, 2), B(10, 6));
                WriteX(D, Logical(ReadX(A, Width), Bit(21) ? Unary(Not, right) : right, B(29, 2))); return;
            }
            if (Is(0x1f200000, 0x0b000000))
            {
                if (B(10, 6) >= Width || B(22, 2) == 3) { Hole(); return; }
                WriteX(D, Arithmetic(ReadX(A, Width), Shift(ReadX(M, Width), B(22, 2), B(10, 6)), Bit(30), Bit(29))); return;
            }
            if (Is(0x1f200000, 0x0b200000))
            {
                if (B(22, 2) != 0 || B(10, 3) > 4) { Hole(); return; }
                var right = Extend(ReadX(M, Math.Min(8 << B(13, 2), Width)), Width, Bit(15));
                WriteX(D, Arithmetic(ReadX(A, Width, true), Shift(right, 0, B(10, 3)), Bit(30), Bit(29)), !Bit(29)); return;
            }
            if (Is(0x1fe0fc00, 0x1a000000))
            {
                WriteX(D, Arithmetic(ReadX(A, Width), ReadX(M, Width), Bit(30), Bit(29), e.Read(C))); return;
            }
            if (Is(0x3fe00410, 0x3a400000))
            {
                var condition = Condition(B(12, 4));
                var a = ReadX(A, Width); var b = Bit(11) ? K(M, Width) : ReadX(M, Width);
                var flags = AddCarry(a, Bit(30) ? Unary(Not, b) : b, K(Bit(30) ? 1 : 0, 1)).Flags;
                Flags(flags.Select((f, i) => Choose(condition, f, K(B(3 - i), 1))).ToArray()); return;
            }
            if (Is(0x3fe00800, 0x1a800000))
            {
                var other = ReadX(M, Width);
                if (Bit(30)) other = Unary(Not, other);
                if (Bit(10)) other = Op(Add, other, K(1, Width));
                WriteX(D, Choose(Condition(B(12, 4)), ReadX(A, Width), other)); return;
            }
            if (Is(0x5fe00000, 0x1ac00000)) { TwoSource(); return; }
            if (Is(0x5fe00000, 0x5ac00000)) { OneSource(); return; }
            if (Is(0x1f000000, 0x1b000000)) { MultiplySource(); return; }
            if (BranchSystem()) return;
            if (Memory()) return;
            if (Is(0x0e000000, 0x0c000000)) { Hole("vector"); return; }
            if (Is(0x0e000000, 0x0e000000)) { Hole(Bit(28) && !Bit(30) ? "floating" : "vector"); return; }
            Hole();
        }
        private void LogicalImmediate()
        {
            int combined = (B(22) << 6) | (~B(10, 6) & 63);
            int length = BitOperations.Log2((uint)combined);
            if (combined == 0 || length < 1 || (Width == 32 && Bit(22))) { Hole(); return; }
            int size = 1 << length, s = B(10, 6) & (size - 1), r = B(16, 6) & (size - 1);
            if (s == size - 1) { Hole(); return; }
            BigInteger element = (BigInteger.One << (s + 1)) - 1, mask = (BigInteger.One << size) - 1;
            element = ((element >> r) | (element << (size - r))) & mask;
            BigInteger immediate = 0;
            for (int i = 0; i < Width; i += size) immediate |= element << i;
            WriteX(D, Logical(ReadX(A, Width), K(immediate, Width), B(29, 2)), B(29, 2) != 3);
        }
        private void Bitfield()
        {
            int r = B(16, 6), s = B(10, 6), opc = B(29, 2);
            if (Bit(22) != Bit(31) || r >= Width || s >= Width || opc == 3) { Hole(); return; }
            int low = s >= r ? 0 : Width - r, count = s >= r ? s - r + 1 : s + 1;
            var field = T.Slice(ReadX(A, Width), s >= r ? r : 0, count);
            if (opc == 1)
            {
                var pieces = new List<Term>(); var old = ReadX(D, Width);
                if (low > 0) pieces.Add(T.Slice(old, 0, low));
                pieces.Add(field);
                if (low + count < Width) pieces.Add(T.Slice(old, low + count, Width - low - count));
                WriteX(D, T.Concat(pieces.ToArray()));
            }
            else WriteX(D, Shift(Extend(field, Width, opc == 0), 0, low));
        }
        private void TwoSource()
        {
            int opcode = B(10, 6);
            if (Bit(29) || opcode is not (2 or 3 or 8 or 9 or 10 or 11)) { Hole("integer-extension"); return; }
            var a = ReadX(A, Width); var b = ReadX(M, Width);
            if (opcode >= 8) { WriteX(D, Shift(a, opcode - 8, Op(And, b, K(Width - 1, Width)))); return; }
            var quotient = Op(opcode == 2 ? UnsignedDivide : SignedDivide, a, b);
            if (opcode == 3)
                quotient = Choose(Op(And, Compare(Equal, a, K(BigInteger.One << (Width - 1), Width)), Compare(Equal, b, K(-1, Width))), a, quotient);
            WriteX(D, Choose(Compare(Equal, b, K(0, Width)), K(0, Width), quotient));
        }
        private void OneSource()
        {
            int opcode = B(10, 6);
            if (Bit(29) || M != 0 || opcode > 5 || (opcode == 3 && Width == 32)) { Hole("integer-extension"); return; }
            var a = ReadX(A, Width);
            if (opcode == 0) WriteX(D, Unary(ReverseBits, a));
            else if (opcode == 4) WriteX(D, Unary(CountLeadingZeros, a));
            else if (opcode == 5)
            {
                var adjusted = Choose(T.Slice(a, Width - 1, 1), Unary(Not, a), a);
                WriteX(D, Op(Subtract, Unary(CountLeadingZeros, adjusted), K(1, Width)));
            }
            else
            {
                int size = 8 << opcode;
                WriteX(D, T.Concat(Enumerable.Range(0, Width / size).Select(i => Unary(ReverseBytes, T.Slice(a, i * size, size))).ToArray()));
            }
        }
        private void MultiplySource()
        {
            int opcode = B(21, 3), accumulator = B(10, 5);
            if (B(29, 2) != 0 || (opcode != 0 && Width != 64)) { Hole(); return; }
            if (opcode is 2 or 6 && !Bit(15) && accumulator == 31)
            { WriteX(D, Op(opcode == 2 ? SignedMultiplyHigh : UnsignedMultiplyHigh, ReadX(A, 64), ReadX(M, 64))); return; }
            if (opcode is not (0 or 1 or 5)) { Hole(); return; }
            int inputWidth = opcode == 0 ? Width : 32;
            var product = Op(Multiply, Extend(ReadX(A, inputWidth), Width, opcode == 1), Extend(ReadX(M, inputWidth), Width, opcode == 1));
            WriteX(D, Op(Bit(15) ? Subtract : Add, ReadX(accumulator, Width), product));
        }
    }
}
