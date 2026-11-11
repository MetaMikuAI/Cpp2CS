using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;
using Cpp2CS.Targets.Arm64;
using Cpp2CS.Targets.Frontend;
using static Cpp2CS.Native.Terms.CoreOperation;

namespace Cpp2CS.Tests;

internal static class IndirectChecks
{
    public const string Command = "indirect";
    public static int Run()
    {
        var checks = new Assertions();
        var t = new TermTable(); var image = new Image();
        Term Op(CoreOperation op, int width, params Term[] values) => t.Apply(new CoreOperator(op), width, values);
        var root = t.Atom(new RootAtom(AddressRoot.Image), 64);
        var index = t.Atom(new EntryAtom(new(SlotKind.Integer)), 32);
        var bounded = t.Slice(index, 0, 1);
        Term Address(Term selector, int bytes) => Op(Add, 64, Op(Add, 64, root, t.Constant(256, 64)),
            Op(Multiply, 64, Op(ZeroExtend, 64, selector), t.Constant(bytes, 64)));
        (Context Context, Term Value) Read(Term selector, int width)
        {
            var id = new ReadIdentity(); var value = t.Atom(new ResultAtom(id), width);
            return (new(t, image, new(id, Address(selector, width / 8), width, value)), value);
        }
        image.Values[256] = 16; image.Values[264] = 20;
        var absolute = Read(bounded, 64);
        var resolved = IndirectResolver.Resolve(absolute.Value, absolute.Context) as IndirectTable;
        checks.True(resolved?.Cases.Select(c => c.Target).SequenceEqual(new ulong[] { 16, 20 }) == true, "绝对地址表，位宽证明范围");
        var relative = Read(bounded, 8);
        image.Values[256] = 0xfc; image.Values[257] = 4;
        var relativeTarget = Op(Add, 64, Op(Add, 64, root, t.Constant(20, 64)), Op(SignExtend, 64, relative.Value));
        resolved = IndirectResolver.Resolve(relativeTarget, relative.Context) as IndirectTable;
        checks.True(resolved?.Cases.Select(c => c.Target).SequenceEqual(new ulong[] { 16, 24 }) == true, "有符号窄元素相对表");
        var calculatedIndex = Op(Multiply, 32, index, t.Constant(7, 32));
        var calculated = Read(calculatedIndex, 8);
        calculated.Context.Conditions = [new(Op(UnsignedLess, 1, calculatedIndex, t.Constant(2, 32)), true)];
        var calculatedTarget = Op(Add, 64, Op(Add, 64, root, t.Constant(20, 64)), Op(SignExtend, 64, calculated.Value));
        checks.True(IndirectResolver.Resolve(calculatedTarget, calculated.Context) is IndirectTable { Cases.Length: 2 }, "字节表的整个算术项是下标，不把下标内的乘法当成步长");
        image.Values[256] = 16; image.Values[264] = 20;
        var path = Read(index, 64);
        path.Context.Conditions = [new(Op(UnsignedLess, 1, index, t.Constant(2, 32)), true)];
        checks.True(IndirectResolver.Resolve(path.Value, path.Context) is IndirectTable { Cases.Length: 2 }, "路径条件证明上界");
        var extended = Op(ZeroExtend, 33, index);
        var carry = t.Slice(Op(Add, 33, extended, t.Constant((System.Numerics.BigInteger.One << 32) - 2, 33)), 32, 1);
        path.Context.Conditions = [new(carry, false)];
        checks.True(IndirectResolver.Resolve(path.Value, path.Context) is IndirectTable { Cases.Length: 2 }, "扩展加法的进位为假证明上界");
        var shifted = Op(Add, 32, index, t.Constant(uint.MaxValue - 2, 32));
        var adjusted = Read(shifted, 64);
        var adjustedCarry = t.Slice(Op(Add, 33, Op(ZeroExtend, 33, shifted), t.Constant((System.Numerics.BigInteger.One << 32) - 1, 33)), 32, 1);
        adjusted.Context.Conditions = [new(Op(And, 1, adjustedCarry, Op(Not, 1, Op(Equal, 1, index, t.Constant(4, 32)))), false)];
        checks.True(IndirectResolver.Resolve(adjusted.Value, adjusted.Context) is IndirectTable { Cases.Length: 2 }, "偏移后的下标由进位与等值边界共同约束");
        path.Context.Conditions = [];
        checks.True(IndirectResolver.Resolve(path.Value, path.Context) is IndirectUnknown { Reason.Code: "indirect.bound" }, "没有上界必须报洞");
        image.Values[264] = 1000;
        checks.True(IndirectResolver.Resolve(absolute.Value, absolute.Context) is IndirectUnknown { Reason.Code: "indirect.target-range" }, "目标出了函数范围");
        image.Writable = true;
        checks.True(IndirectResolver.Resolve(absolute.Value, absolute.Context) is IndirectUnknown { Reason.Code: "indirect.storage" }, "可写表不能解析，也不能误作尾调用");
        image.Writable = false;
        var isa = new Toy(false);
        var range = new FunctionRange(0, 2, FunctionEvidence.SymbolTable);
        var tail = FunctionLifter.Lift(isa, Arm64Registers.Convention, new Arm64FlowFacts(), range, 0);
        checks.True(tail.Function is { } f && f.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ComputedTarget
            && f.Blocks.Any(b => b.End is Return), "经寄存器尾调用写成调用加返回");
        checks.True(FunctionLifter.Lift(new Toy(true), Arm64Registers.Convention, new Arm64FlowFacts(), range, 0)
            .Failure?.Reason.Code == "stack-restore", "间接尾调用必须复位栈指针");
        image.Code = true; image.Values[0] = 0xd65f0000;
        checks.True(FunctionLifter.Lift(new Arm64InstructionSet(image), Arm64Registers.Convention, new Arm64FlowFacts(),
            new(0, 4, FunctionEvidence.SymbolTable), 0).Failure?.Reason.Code == "arm64.indirect-ret", "非默认 RET 明确报洞");
        return checks.Finish("间接跳转");
    }
    private sealed class Context(TermTable terms, IImage image, MemoryRead read) : IIndirectContext
    {
        public TermTable Terms => terms;
        public IImage Image => image;
        public FunctionRange Range => new(0, 64, FunctionEvidence.SymbolTable);
        public ImmutableArray<FlowCondition> Conditions { get; set; } = [];
        public Term? InUniquePredecessor(Term input) => null;
        public MemoryRead? ReadOf(Term result) => result == read.Result ? read : null;
    }
    private sealed class Toy(bool changeStack) : IInstructionSet
    {
        public ImmutableArray<Register> Registers => Arm64Registers.All;
        public DecodeResult Decode(ulong address) => new(new(1, e =>
        {
            if (address == 0)
            {
                if (changeStack) e.Write(Arm64Registers.Sp, e.Terms.Apply(new CoreOperator(Subtract), 64,
                    e.Read(Arm64Registers.Sp), e.Terms.Constant(16, 64)));
            }
            else e.IndirectJump(e.Read(Arm64Registers.X[0]));
        }), null);
    }
    private sealed class Image : IImage
    {
        internal readonly Dictionary<ulong, ulong> Values = [];
        internal bool Writable;
        internal bool Code;
        public ulong PreferredBase => 0;
        public int PointerWidth => 8;
        public ByteOrder ByteOrder => ByteOrder.LittleEndian;
        public ImmutableArray<ImageRange> Ranges => [new(256, 256, StorageKind.FileContent, false, Writable)];
        public IReadOnlyList<ImageRelocation> Relocations => [];
        public ImmutableArray<ImportSymbol> Imports => [];
        public ImmutableArray<ExportSymbol> Exports => [];
        public ImmutableArray<FunctionSymbol> FunctionSymbols => [];
        public ImmutableArray<FunctionRange> Functions => [];
        public ImmutableArray<TryRegion> TryRegions => [];
        public ImmutableArray<string> Diagnostics => [];
        public AddressInfo Query(ulong offset) => offset >= 256 && offset < 512
            ? new(StorageKind.FileContent, 512 - offset, false, Writable) : new(StorageKind.Unmapped, 0, false, false);
        public bool IsExecutable(ulong offset, ulong length = 1) => Code && offset == 0 && length <= 4;
        public bool IsWritable(ulong offset, ulong length = 1) => Writable;
        public ulong ReadUnsigned(ulong offset, int width) => Values[offset];
        public PointerTarget ReadPointer(ulong offset) => new PointerTarget.Internal(Values[offset]);
        public void ReadBytes(ulong offset, Span<byte> destination) => throw new NotSupportedException();
    }
}
