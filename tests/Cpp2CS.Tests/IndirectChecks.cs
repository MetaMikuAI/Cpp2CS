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
            return (new(t, image, new MemoryRead(id, Address(selector, width / 8), width, value)), value);
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
        checks.True(IndirectResolver.Resolve(absolute.Value, absolute.Context) is IndirectTailCall, "根全部在可写段的读取属于运行期目标");
        image.Writable = false;
        GlobalsAndMerges(checks, t, image);
        TwoLevelTables(checks, t, image);
        var isa = new Toy(false);
        var range = new FunctionRange(0, 2, FunctionEvidence.SymbolTable);
        var tail = FunctionLifter.Lift(isa, Arm64Registers.Convention, new Arm64FlowFacts(), range, 0);
        checks.True(tail.Function is { } f && f.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ComputedTarget
            && f.Blocks.Any(b => b.End is Return), "经寄存器尾调用写成调用加返回");
        checks.True(FunctionLifter.Lift(new Toy(true), Arm64Registers.Convention, new Arm64FlowFacts(), range, 0)
            .Failure?.Reason.Code == "stack-restore", "间接尾调用必须复位栈指针");
        image.Writable = true;
        var global = FunctionLifter.Lift(new Toy(false, image), Arm64Registers.Convention, new Arm64FlowFacts(), range, 0);
        checks.True(global.Function?.Blocks.SelectMany(b => b.Statements).OfType<Call>().Single().Target is ComputedTarget,
            "可写全局读取提升为调用加返回");
        checks.True(FunctionLifter.Lift(new Toy(true, image), Arm64Registers.Convention, new Arm64FlowFacts(), range, 0)
            .Failure?.Reason.Code == "stack-restore", "可写全局尾调用仍须复位栈指针");
        image.Code = true; image.Values[0] = 0xd65f0000;
        checks.True(FunctionLifter.Lift(new Arm64InstructionSet(image), Arm64Registers.Convention, new Arm64FlowFacts(),
            new(0, 4, FunctionEvidence.SymbolTable), 0).Failure?.Reason.Code == "arm64.indirect-ret", "非默认 RET 明确报洞");
        return checks.Finish("间接跳转");
    }
    private static void GlobalsAndMerges(Assertions checks, TermTable t, Image image)
    {
        var root = t.Atom(new RootAtom(AddressRoot.Image), 64);
        Term Address(ulong offset) => t.Apply(new CoreOperator(Add), 64, root, t.Constant(offset, 64));
        MemoryRead Read(Term address)
        {
            var id = new ReadIdentity(); return new(id, address, 64, t.Atom(new ResultAtom(id), 64));
        }
        var read = Read(Address(256)); var context = new Context(t, image, read);
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectUnknown { Reason.Code: "indirect.shape" },
            "只读常量槽没有下标和重定位仍是洞");
        image.Writable = true;
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectTailCall, "固定可写全局槽是尾调用");
        var merged = t.Atom(new EntryAtom(new(SlotKind.Integer, 2)), 64);
        read = Read(merged); context = new(t, image, read);
        context.Sources[merged] = [Address(256), Address(384)];
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectTailCall, "合流的全部映像根可写时是尾调用");
        image.ReadOnlyStart = 384;
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectUnknown { Reason.Code: "indirect.merge" }, "合流含一个只读根仍是洞");
        context.Sources[merged] = [Address(384), t.Atom(new EntryAtom(new(SlotKind.Integer, 3)), 64)];
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectUnknown { Reason.Code: "indirect.merge" }, "只读根与非映像来源合流仍是洞");
        context.Sources[merged] = [Address(256), merged];
        checks.True(IndirectResolver.Resolve(read.Result, context) is IndirectTailCall, "可写根的循环合流有限收敛");
        var got = Read(Address(384)); var runtime = Read(got.Result);
        image.Relocations = [new(384, 8, RelocationKind.Pointer, new PointerTarget.Internal(256))];
        image.Pointers[384] = new PointerTarget.Internal(256);
        checks.True(IndirectResolver.Resolve(runtime.Result, new Context(t, image, got, runtime)) is IndirectTailCall,
            "先按只读重定位解开 GOT，再判断可写全局的运行期读取");
        image.Relocations = []; image.Pointers.Clear();
        image.Writable = false; image.ReadOnlyStart = 4096;
    }
    private static void TwoLevelTables(Assertions checks, TermTable t, Image image)
    {
        var root = t.Atom(new RootAtom(AddressRoot.Image), 64);
        var index = t.Slice(t.Atom(new EntryAtom(new(SlotKind.Integer, 4)), 32), 0, 1);
        MemoryRead Read(Term selector, ulong offset, int width)
        {
            var scaled = t.Apply(new CoreOperator(Multiply), 64, t.Apply(new CoreOperator(ZeroExtend), 64, selector), t.Constant((ulong)width / 8, 64));
            var address = t.Apply(new CoreOperator(Add), 64, root, t.Apply(new CoreOperator(Add), 64, t.Constant(offset, 64), scaled));
            var id = new ReadIdentity(); return new(id, address, width, t.Atom(new ResultAtom(id), width));
        }
        var first = Read(index, 256, 8); var second = Read(first.Result, 512, 64);
        image.Values[256] = 1; image.Values[257] = 0; image.Values[512] = 16; image.Values[520] = 20;
        var context = new Context(t, image, first, second);
        var resolved = IndirectResolver.Resolve(second.Result, context) as IndirectTable;
        checks.True(resolved?.Selector == index && resolved.Cases.Select(c => c.Target).SequenceEqual(new ulong[] { 20, 16 }), "两级只读表逐下标计算目标");
        first = Read(index, 256, 32); second = Read(first.Result, 512, 64);
        checks.True(IndirectResolver.Resolve(second.Result, new Context(t, image, first, second)) is IndirectUnknown { Reason.Code: "indirect.bound" },
            "第二级没有已证明的可枚举上界时仍是洞");
    }
    private sealed class Context(TermTable terms, IImage image, params MemoryRead[] reads) : IIndirectContext
    {
        public TermTable Terms => terms;
        public IImage Image => image;
        public FunctionRange Range => new(0, 64, FunctionEvidence.SymbolTable);
        public ImmutableArray<FlowCondition> Conditions { get; set; } = [];
        public Term? InUniquePredecessor(Term input) => null;
        internal Dictionary<Term, ImmutableArray<Term>> Sources { get; } = [];
        public ImmutableArray<Term> InPredecessors(Term input) => Sources.GetValueOrDefault(input, []);
        public MemoryRead? ReadOf(Term result) => reads.FirstOrDefault(r => r.Result == result);
    }
    private sealed class Toy(bool changeStack, IImage? image = null) : IInstructionSet, IImageInstructionSet
    {
        public IImage Image { get; } = image ?? new Image();
        public ImmutableArray<Register> Registers => Arm64Registers.All;
        public DecodeResult Decode(ulong address) => new(new(1, e =>
        {
            if (address == 0)
            {
                if (changeStack) e.Write(Arm64Registers.Sp, e.Terms.Apply(new CoreOperator(Subtract), 64,
                    e.Read(Arm64Registers.Sp), e.Terms.Constant(16, 64)));
            }
            else e.IndirectJump(image is null ? e.Read(Arm64Registers.X[0]) : e.Load(e.ImageAddress(256), 64));
        }), null);
    }
    private sealed class Image : IImage
    {
        internal readonly Dictionary<ulong, ulong> Values = [];
        internal readonly Dictionary<ulong, PointerTarget> Pointers = [];
        internal bool Writable;
        internal ulong ReadOnlyStart = 4096;
        internal bool Code;
        public ulong PreferredBase => 0;
        public int PointerWidth => 8;
        public ByteOrder ByteOrder => ByteOrder.LittleEndian;
        public ImmutableArray<ImageRange> Ranges => [new(256, 3840, StorageKind.FileContent, false, Writable)];
        public IReadOnlyList<ImageRelocation> Relocations { get; set; } = [];
        public ImmutableArray<ImportSymbol> Imports => [];
        public ImmutableArray<ExportSymbol> Exports => [];
        public ImmutableArray<FunctionSymbol> FunctionSymbols => [];
        public ImmutableArray<FunctionRange> Functions => [];
        public ImmutableArray<TryRegion> TryRegions => [];
        public ImmutableArray<string> Diagnostics => [];
        public AddressInfo Query(ulong offset) => offset >= 256 && offset < 4096
            ? new(StorageKind.FileContent, (offset < ReadOnlyStart ? ReadOnlyStart : 4096) - offset, false, Writable && offset < ReadOnlyStart)
            : new(StorageKind.Unmapped, 0, false, false);
        public bool IsExecutable(ulong offset, ulong length = 1) => Code && offset == 0 && length <= 4;
        public bool IsWritable(ulong offset, ulong length = 1) => Query(offset) is { Writable: true } info && info.AvailableBytes >= length;
        public ulong ReadUnsigned(ulong offset, int width) => Values[offset];
        public PointerTarget ReadPointer(ulong offset) => Pointers.GetValueOrDefault(offset) ?? new PointerTarget.Internal(Values[offset]);
        public void ReadBytes(ulong offset, Span<byte> destination) => throw new NotSupportedException();
    }
}
