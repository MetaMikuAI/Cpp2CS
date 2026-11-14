using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Images;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Tests;

/// <summary>映像里不变的数据：读取得到文件内容或重定位指向的映像地址。</summary>
internal static class StateImageChecks
{
    public const string Command = "state-image";

    // [0, 0x100) 只读；[0x100, 0x200) 可写。0x10 处有一个指向 0x180 的指针重定位，0x20 处是普通常量。
    private sealed class Image : IImage
    {
        private readonly byte[] bytes = new byte[0x200];
        private readonly ByteOrder order;
        public Image(ByteOrder order = ByteOrder.LittleEndian)
        {
            this.order = order;
            BitConverter.TryWriteBytes(bytes.AsSpan(0x20), 0x1122334455667788UL);
            BitConverter.TryWriteBytes(bytes.AsSpan(0x28), 0x99aabbccddeeff00UL);
            BitConverter.TryWriteBytes(bytes.AsSpan(0x30), 0x0123456789abcdefUL);
            BitConverter.TryWriteBytes(bytes.AsSpan(0x38), 0xfedcba9876543210UL);
        }
        public ulong PreferredBase => 0;
        public int PointerWidth => 8;
        public ByteOrder ByteOrder => order;
        public ImmutableArray<ImageRange> Ranges => [new(0, 0x100, StorageKind.FileContent, false, false), new(0x100, 0x100, StorageKind.FileContent, false, true)];
        public IReadOnlyList<ImageRelocation> Relocations { get; } = [new(0x10, 8, RelocationKind.Pointer, new PointerTarget.Internal(0x180))];
        public ImmutableArray<ImportSymbol> Imports => [];
        public ImmutableArray<ExportSymbol> Exports => [];
        public ImmutableArray<FunctionSymbol> FunctionSymbols => [];
        public ImmutableArray<FunctionRange> Functions => [];
        public ImmutableArray<TryRegion> TryRegions => [];
        public ImmutableArray<string> Diagnostics => [];
        public AddressInfo Query(ulong offset) => offset < 0x100 ? new(StorageKind.FileContent, 0x100 - offset, false, false)
            : offset < 0x200 ? new(StorageKind.FileContent, 0x200 - offset, false, true) : new(StorageKind.Unmapped, 0, false, false);
        public bool IsExecutable(ulong offset, ulong length = 1) => false;
        public bool IsWritable(ulong offset, ulong length = 1) => offset >= 0x100;
        public void ReadBytes(ulong offset, Span<byte> destination) => bytes.AsSpan(checked((int)offset), destination.Length).CopyTo(destination);
        public ulong ReadUnsigned(ulong offset, int width)
        {
            ulong value = 0;
            for (var i = 0; i < width; i++)
                if (order == ByteOrder.LittleEndian) value |= (ulong)bytes[checked((int)offset + i)] << (i * 8);
                else value = (value << 8) | bytes[checked((int)offset + i)];
            return value;
        }
        public PointerTarget ReadPointer(ulong offset) => offset == 0x10 ? new PointerTarget.Internal(0x180)
            : ReadUnsigned(offset, 8) == 0 ? new PointerTarget.Null() : new PointerTarget.NotPointer("无重定位");
    }

    public static int Run()
    {
        var checks = new Assertions();
        var terms = new TermTable();
        var entry = new BlockIdentity();
        var frame = terms.Atom(new RootAtom(AddressRoot.Frame), 64);
        var imageBase = terms.Atom(new RootAtom(AddressRoot.Image), 64);
        Term At(ulong offset) => terms.Apply(new CoreOperator(CoreOperation.Add), 64, imageBase, terms.Constant(offset, 64));
        MemoryRead Read(Term address, int width) { var id = new ReadIdentity(); return new(id, address, width, terms.Atom(new ResultAtom(id), width)); }

        var constant = Read(At(0x20), 64);
        var narrow = Read(At(0x20), 32);
        var call = new Call(new(), new ImageFunction(0x1000), [], []);
        var afterCall = Read(At(0x20), 64);
        var pointer = Read(At(0x10), 64);
        var through = Read(pointer.Result, 64);
        var partial = Read(At(0x10), 32);
        var writable = Read(At(0x100), 64);
        var wide = Read(At(0x20), 128); var block = Read(At(0x20), 256);
        var wideRelocation = Read(At(8), 128); var wideBoundary = Read(At(0xf8), 128);
        var builder = new FunctionBuilder(terms, entry, 64, new(frame)) { ImageBase = imageBase };
        builder.Blocks.Add(new(entry, [], [constant, narrow, call, afterCall, pointer, through, partial, writable,
            wide, block, wideRelocation, wideBoundary], new Return([])));
        var function = builder.Freeze();

        var queries = new StateQueries(image: new Image());
        var context = queries.CreateContext(function);
        Term Value(MemoryRead read)
        {
            var result = context.Get(queries.Read, read.Identity);
            return result.IsSuccess ? result.Value : throw new InvalidOperationException(result.Why?.ToString());
        }
        checks.True(Value(constant).ConstantValue == 0x1122334455667788UL, "只读数据的读取是文件里的常量");
        checks.True(Value(narrow).ConstantValue == 0x55667788UL, "窄读取取低位字节");
        checks.True(Value(afterCall).ConstantValue == 0x1122334455667788UL, "未知调用不改写只读数据");
        checks.True(Value(pointer) == At(0x180), "只读的指针重定位读出映像地址");
        var target = context.Get(queries.Locations, new(Value(pointer), 64));
        checks.True(target.IsSuccess && target.Value.Region == Region.Image && target.Value.Offset == 0x180, "读出的地址分解到映像位置");
        checks.True(Value(through).Identity is MemoryAtom { Location: { Region: Region.Image, Offset: var offset } } && offset == 0x180, "经只读指针的读取落在可写数据上，不是常量");
        checks.True(Value(partial).Identity is MemoryAtom, "与重定位部分重叠的读取不解析");
        checks.True(Value(writable).Identity is MemoryAtom, "可写数据的读取不是常量");
        var expected = (new System.Numerics.BigInteger(0x99aabbccddeeff00UL) << 64) | 0x1122334455667788UL;
        checks.True(Value(wide).ConstantValue == expected, "128 位只读字面量保留全部位");
        var high = (new System.Numerics.BigInteger(0xfedcba9876543210UL) << 64) | 0x0123456789abcdefUL;
        checks.True(Value(block).ConstantValue == (high << 128 | expected), "256 位只读块按字节序组成常量");
        checks.True(Value(wideRelocation).Identity is MemoryAtom, "宽读取包含指针重定位时不折成数字");
        checks.True(Value(wideBoundary).Identity is MemoryAtom, "宽读取跨入可写区域时不折叠");
        var big = new StateQueries(image: new Image(ByteOrder.BigEndian));
        var bigValue = big.CreateContext(function).Get(big.Read, wide.Identity);
        checks.True(bigValue.IsSuccess && bigValue.Value.ConstantValue ==
            ((new System.Numerics.BigInteger(0x8877665544332211UL) << 64) | 0x00ffeeddccbbaa99UL), "宽常量读取遵守映像的大端字节序");

        var plain = new StateQueries();
        var plainRead = plain.CreateContext(function).Get(plain.Read, constant.Identity);
        checks.True(plainRead.IsSuccess && plainRead.Value.Identity is MemoryAtom, "没有给出映像时按普通内存处理");
        return checks.Finish("状态模型的映像数据");
    }
}
