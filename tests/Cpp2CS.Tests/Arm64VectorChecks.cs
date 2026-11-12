using System.Numerics;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Frontend;
using static Cpp2CS.Native.Terms.CoreOperation;
using static Cpp2CS.Targets.Arm64.Arm64Registers;

namespace Cpp2CS.Tests;

internal static class Arm64VectorChecks
{
    public const string Command = "arm64-vector";
    public static int Run()
    {
        var checks = new Assertions();
        void Check(uint word, Func<Symbolic, Term> expected, string name)
        {
            var s = new Symbolic();
            Arm64InstructionSet.DecodeWord(0, word).Instruction!.Emit(s);
            checks.True(s.Failure is null && s.Read(V[(int)(word & 31)]) == expected(s), $"{word:x8} {name} 的项与清零位");
        }
        void FloatBinary(uint word, CoreOperation op, int bits, int lanes, bool abs = false) => Check(word, s => s.Pack(Enumerable.Range(0, lanes).Select(i =>
        {
            var value = s.Apply(op, bits, s.Lane((int)(word >> 5 & 31), i, bits), s.Lane((int)(word >> 16 & 31), i, bits));
            return abs ? s.Apply(FloatAbs, bits, value) : value;
        }).ToArray()), "逐元素浮点");
        foreach (var word in new uint[] { 0x5e21d821, 0x7e21da10, 0x5e61d821, 0x7e61d800, 0x0e21d808, 0x6e61d820 })
        {
            int bits = (word & 0x400000) != 0 ? 64 : 32;
            int lanes = (word & 0x10000000) != 0 ? 1 : (word & 0x40000000) != 0 ? 128 / bits : 64 / bits;
            Check(word, s => s.Pack(Enumerable.Range(0, lanes).Select(i => s.Apply((word & 0x20000000) == 0 ? SignedToFloat : UnsignedToFloat,
                bits, s.Lane((int)(word >> 5 & 31), i, bits))).ToArray()), "整数转浮点");
        }
        FloatBinary(0x7ea0d500, FloatSubtract, 32, 1, true);
        FloatBinary(0x7ee0d520, FloatSubtract, 64, 1, true);
        FloatBinary(0x0e22d400, FloatAdd, 32, 2);
        FloatBinary(0x4e21d400, FloatAdd, 32, 4);
        FloatBinary(0x0ea1d408, FloatSubtract, 32, 2);
        FloatBinary(0x4ea1d442, FloatSubtract, 32, 4);
        FloatBinary(0x2e21dc00, FloatMultiply, 32, 2);
        FloatBinary(0x6e22dc00, FloatMultiply, 32, 4);
        FloatBinary(0x2e20fc20, FloatDivide, 32, 2);
        FloatBinary(0x4e62d420, FloatAdd, 64, 2);
        FloatBinary(0x4ee2d420, FloatSubtract, 64, 2);
        FloatBinary(0x6e62dc20, FloatMultiply, 64, 2);
        FloatBinary(0x6e62fc20, FloatDivide, 64, 2);
        FloatBinary(0x6ee2d420, FloatSubtract, 64, 2, true);
        foreach (var (word, bits, lanes, source, lane) in new (uint, int, int, int, int)[]
        {
            (0x0f839103, 32, 2, 3, 0), (0x4f819061, 32, 4, 1, 0), (0x5fa09063, 32, 1, 0, 1),
            (0x0fb29820, 32, 2, 18, 3), (0x4fb29820, 32, 4, 18, 3), (0x4fd29820, 64, 2, 18, 1), (0x5fd29820, 64, 1, 18, 1)
        }) Check(word, s => s.Pack(Enumerable.Range(0, lanes).Select(i => s.Apply(FloatMultiply, bits,
            s.Lane((int)(word >> 5 & 31), i, bits), s.Lane(source, lane, bits))).ToArray()), "按元素乘法的下标与完整寄存器号");
        Check(0x0ea00800, s => s.Pack(s.Lane(0, 1, 32), s.Lane(0, 0, 32)), "REV64 低半");
        Check(0x4ea00821, s => s.Pack(s.Lane(1, 1, 32), s.Lane(1, 0, 32), s.Lane(1, 3, 32), s.Lane(1, 2, 32)), "REV64 分别反转两个块");
        Check(0x6e002001, s => s.Pack(s.Terms.Slice(s.Terms.Concat(s.Input(V[0]), s.Input(V[0])), 32, 128)), "EXT 四字节");
        Check(0x6e004001, s => s.Pack(s.Terms.Slice(s.Terms.Concat(s.Input(V[0]), s.Input(V[0])), 64, 128)), "EXT 八字节");
        Check(0x2e023820, s => s.Pack(s.Terms.Slice(s.Terms.Concat(s.Terms.Slice(s.Input(V[1]), 0, 64), s.Terms.Slice(s.Input(V[2]), 0, 64)), 56, 64)), "EXT 的 Q=0 只读两个低半");
        Check(0x0ea0f800, s => s.Pack(s.Apply(FloatAbs, 32, s.Lane(0, 0, 32)), s.Apply(FloatAbs, 32, s.Lane(0, 1, 32))), "向量绝对值");
        Check(0x0ea08442, s => s.Pack(s.Apply(Add, 32, s.Lane(2, 0, 32), s.Lane(0, 0, 32)), s.Apply(Add, 32, s.Lane(2, 1, 32), s.Lane(0, 1, 32))), "整数加法");
        Check(0x2ea08420, s => s.Pack(s.Apply(Subtract, 32, s.Lane(1, 0, 32), s.Lane(0, 0, 32)), s.Apply(Subtract, 32, s.Lane(1, 1, 32), s.Lane(0, 1, 32))), "整数减法");
        Check(0x4ea19c00, s => s.Pack(Enumerable.Range(0, 4).Select(i => s.Apply(Multiply, 32, s.Lane(0, i, 32), s.Lane(1, i, 32))).ToArray()), "整数乘法");
        Check(0x4ee18400, s => s.Pack(s.Apply(Add, 64, s.Lane(0, 0, 64), s.Lane(1, 0, 64)), s.Apply(Add, 64, s.Lane(0, 1, 64), s.Lane(1, 1, 64))), "双字整数加法");
        Check(0x0ea16400, s => s.Pack(Enumerable.Range(0, 2).Select(i => s.Apply(Select, 32, s.Apply(SignedLess, 1, s.Lane(0, i, 32), s.Lane(1, i, 32)), s.Lane(1, i, 32), s.Lane(0, i, 32))).ToArray()), "有符号最大值");
        Check(0x0ea16c00, s => s.Pack(Enumerable.Range(0, 2).Select(i => s.Apply(Select, 32, s.Apply(SignedLess, 1, s.Lane(0, i, 32), s.Lane(1, i, 32)), s.Lane(0, i, 32), s.Lane(1, i, 32))).ToArray()), "有符号最小值");
        Check(0x0ea23420, s => s.Pack(Enumerable.Range(0, 2).Select(i => s.Apply(Select, 32, s.Apply(SignedLess, 1, s.Lane(2, i, 32), s.Lane(1, i, 32)), s.Terms.Constant(uint.MaxValue, 32), s.Terms.Constant(0, 32))).ToArray()), "比较真值填满元素");
        Check(0x4ee23420, s => s.Pack(Enumerable.Range(0, 2).Select(i => s.Apply(Select, 64, s.Apply(SignedLess, 1, s.Lane(2, i, 64), s.Lane(1, i, 64)), s.Terms.Constant(ulong.MaxValue, 64), s.Terms.Constant(0, 64))).ToArray()), "双字比较真值填满元素");
        Check(0x4eb1b800, s => s.Pack(s.Apply(Add, 32, s.Apply(Add, 32, s.Apply(Add, 32, s.Lane(0, 0, 32), s.Lane(0, 1, 32)), s.Lane(0, 2, 32)), s.Lane(0, 3, 32))), "ADDV 归约只写标量");
        Memory(checks);
        FixedPoint(checks);
        Reject(checks);
        return checks.Finish("ARM64 向量项");
    }
    private static void Memory(Assertions checks)
    {
        foreach (var (word, bits, lane, replicate, load, post, source) in new (uint, int, int, bool, bool, bool, int)[]
        {
            (0x0d4091a0, 32, 1, false, true, false, 13), (0x4d40c942, 32, 0, true, true, false, 10),
            (0x0d009120, 32, 1, false, false, false, 9), (0x0ddf9120, 32, 1, false, true, true, 9),
            (0x4dc2c942, 32, 0, true, true, true, 10),
            (0x0d9f9120, 32, 1, false, false, true, 9), (0x0dc99120, 32, 1, false, true, true, 9),
            (0x0ddf93e0, 32, 1, false, true, true, 31)
        })
        {
            var s = new Symbolic(); Arm64InstructionSet.DecodeWord(0, word).Instruction!.Emit(s);
            var access = load ? s.Loads.Single() : (s.Stores.Single().Address, s.Stores.Single().Value);
            checks.True(s.Failure is null && access.Item1 == s.Input(source == 31 ? Sp : X[source]) && access.Item2.Width == bits, $"{word:x8} 单元素访存地址和宽度");
            int d = (int)(word & 31);
            var expected = !load ? s.Input(V[d]) : replicate ? s.Pack(Enumerable.Repeat(access.Item2, (word & 0x40000000) == 0 ? 64 / bits : 128 / bits).ToArray())
                : s.Terms.Concat(s.Terms.Slice(s.Input(V[d]), 0, lane * bits), access.Item2, s.Terms.Slice(s.Input(V[d]), (lane + 1) * bits, 128 - (lane + 1) * bits));
            checks.True(s.Read(V[d]) == expected && (load || access.Item2 == s.Lane(d, lane, bits)), $"{word:x8} 保留未访问车道或复制元素");
            if (post)
            {
                int m = (int)(word >> 16 & 31);
                var increment = m == 31 ? s.Terms.Constant(bits / 8, 64) : s.Input(X[m]);
                checks.True(s.Read(source == 31 ? Sp : X[source]) == s.Apply(Add, 64, s.Input(source == 31 ? Sp : X[source]), increment), "后变址用访存前基址与增量更新");
            }
        }
    }
    private static void FixedPoint(Assertions checks)
    {
        foreach (var (bits, expected) in new (uint, uint)[] { (0x3fc00000, 1536), (0xbfc00000, unchecked((uint)-1536)), (0x7fc00000, 0), (0x7f800000, int.MaxValue), (0xff800000, 0x80000000) })
        {
            var s = new Arm64Checks.Concrete();
            s.Write(V[0], s.Terms.Constant(((BigInteger.One << 96) - 1) << 32 | bits, 128));
            Arm64InstructionSet.DecodeWord(0, 0x1e18d808).Instruction!.Emit(s);
            var value = new TermEvaluator(_ => throw new InvalidOperationException()).Evaluate(s.Read(X[8]));
            checks.True(s.Failure is null && value.Status == EvaluationStatus.Defined && value.Bits == expected, "FCVTZS #10 缩放、饱和与 W 写入清零");
        }
        foreach (var word in new uint[] { 0x1e19d808, 0x1e180008 })
        {
            var s = new Symbolic(); Arm64InstructionSet.DecodeWord(0, word).Instruction!.Emit(s);
            checks.True(s.Failure is { Code: "arm64.floating" } f && f.Message.Contains("浮点转定点", StringComparison.Ordinal)
                && f.Message.Contains("scale=", StringComparison.Ordinal) && s.Writes == 0, "未支持的定点转换和保留 scale 报洞");
        }
    }
    private static void Reject(Assertions checks)
    {
        foreach (var (word, encoding) in new (uint, string)[]
        {
            (0x0e61d820, "向量二寄存器杂项"), (0x5ea1d820, "标量二寄存器杂项"),
            (0x0e62d420, "向量三操作数同型"), (0x0e22f420, "向量三操作数同型"), (0x4e22cc20, "向量三操作数同型"),
            (0x5e22d420, "标量三操作数同型"), (0x4ff29820, "向量按元素运算"), (0x0fd29820, "向量按元素运算"), (0x4fb21820, "向量按元素运算"),
            (0x2e024020, "向量提取"), (0x4df0c920, "向量单结构访存"), (0x6ee0b820, "向量二寄存器杂项"), (0x6ee23c20, "向量三操作数同型"), (0x0eb1b820, "向量跨元素归约")
        })
        {
            var s = new Symbolic(); Arm64InstructionSet.DecodeWord(0, word).Instruction!.Emit(s);
            checks.True(s.Failure is { Code: "arm64.vector" } f && f.Message.Contains(encoding, StringComparison.Ordinal)
                && f.Message.Contains("0x" + word.ToString("x8"), StringComparison.Ordinal) && s.Writes == 0 && s.Loads.Count == 0 && s.Stores.Count == 0,
                $"{word:x8} 未实现或保留编码有编码类原因且无部分效果");
        }
    }
    private sealed class Symbolic : IEmitter
    {
        public TermTable Terms { get; } = new();
        private readonly Dictionary<Register, Term> initial = [];
        private readonly Dictionary<Register, Term> state = [];
        public List<(Term Address, Term Value)> Loads { get; } = [];
        public List<(Term Address, Term Value)> Stores { get; } = [];
        public Reason? Failure { get; private set; }
        public int Writes { get; private set; }
        public Symbolic()
        {
            foreach (var register in All) state[register] = initial[register] = Terms.Unknown(register.Width, new("check.input", register.Name));
        }
        public Term Input(Register register) => initial[register];
        public Term Lane(int register, int lane, int bits) => Terms.Slice(Input(V[register]), lane * bits, bits);
        public Term Pack(params Term[] elements)
        {
            var value = Terms.Concat(elements);
            return value.Width == 128 ? value : Terms.Concat(value, Terms.Constant(0, 128 - value.Width));
        }
        public Term Apply(CoreOperation op, int width, params Term[] args) => Terms.Apply(new CoreOperator(op), width, args);
        public Term Read(Register register) => state[register];
        public void Write(Register register, Term value) { Writes++; state[register] = value; }
        public Term Load(Term address, int width)
        {
            var value = Terms.Unknown(width, new("check.load", "读取")); Loads.Add((address, value)); return value;
        }
        public void Store(Term address, Term value) => Stores.Add((address, value));
        public void Fail(Reason reason) => Failure = reason;
        public Term ImageAddress(ulong offset) => Terms.Constant(offset, 64);
        public Term ThreadPointer => Terms.Unknown(64, new("check.thread", "线程"));
        public void Call(CallTarget target) => throw new InvalidOperationException();
        public void Jump(ulong target) => throw new InvalidOperationException();
        public void Branch(Term condition, ulong whenTrue, ulong whenFalse) => throw new InvalidOperationException();
        public void IndirectJump(Term target) => throw new InvalidOperationException();
        public void Return() => throw new InvalidOperationException();
        public void Trap() => throw new InvalidOperationException();
        public void TrapIf(Term condition) => throw new InvalidOperationException();
    }
}
