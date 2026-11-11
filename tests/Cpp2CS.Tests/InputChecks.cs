using System.Buffers.Binary;
using System.Collections.Immutable;
using Cpp2CS.Input;
using Cpp2CS.Native.Images;
using Il2CppDumper;
namespace Cpp2CS.Tests;

internal static class InputChecks
{
    public const string Command = "input";
    public static int Run()
    {
        var a = new Assertions();
        var spec = InputCorpusChecks.Spec("arm64-v8a");
        var image = new InputMemoryImage();
        var header = new byte[1024];
        BinaryPrimitives.WriteUInt32LittleEndian(header, 0xFAB11BAF);
        BinaryPrimitives.WriteInt32LittleEndian(header.AsSpan(4), 32);
        Reject<NotSupportedException>(() => ModelBuilder.Read(image, new MemoryStream(header), spec), "不支持的元数据版本");
        BinaryPrimitives.WriteInt32LittleEndian(header.AsSpan(4), 31);
        Reject<InvalidDataException>(() => ModelBuilder.Read(image, new MemoryStream(header), spec), "注册表定位失败");
        using var metadata = new Metadata(new MemoryStream(header));
        var data = new RuntimeData(image, spec);
        image.Put(data.Offset("Il2CppMetadataRegistration", "fieldOffsetsCount"), 1, sizeof(int));
        Reject<InvalidDataException>(() => data.Initialize(0, metadata), "映像与元数据不匹配");
        image.Put(256, 0x123456789, 8);
        image.Pointers[256] = new PointerTarget.Internal(512);
        a.True(data.Pointer(256) == 512, "指针以重定位结果为准，不取原始字节");
        image.Pointers[256] = new PointerTarget.Import(new("external"));
        Reject<InvalidDataException>(() => data.Pointer(256), "不是内部指针");
        return a.Finish("Input 快速检查");
        void Reject<T>(Action action, string diagnostic) where T : Exception
        {
            try { action(); a.True(false, diagnostic); }
            catch (T e) { a.True(e.Message.Contains(diagnostic, StringComparison.Ordinal), $"失败信息应说明 {diagnostic}：{e.Message}"); }
        }
    }
}

internal sealed class InputMemoryImage : IImage
{
    private readonly byte[] bytes = new byte[4096];
    public Dictionary<ulong, PointerTarget> Pointers { get; } = [];
    public ulong PreferredBase => 0x400000;
    public int PointerWidth => 8;
    public ByteOrder ByteOrder => ByteOrder.LittleEndian;
    public ImmutableArray<ImageRange> Ranges => [new(0, (ulong)bytes.Length, StorageKind.FileContent, false, true)];
    public IReadOnlyList<ImageRelocation> Relocations => [];
    public ImmutableArray<ImportSymbol> Imports => [];
    public ImmutableArray<ExportSymbol> Exports => [];
    public ImmutableArray<FunctionSymbol> FunctionSymbols { get; init; } = [];
    public ImmutableArray<FunctionRange> Functions => [];
    public ImmutableArray<TryRegion> TryRegions => [];
    public ImmutableArray<string> Diagnostics => [];
    public AddressInfo Query(ulong offset) => offset < (ulong)bytes.Length ? new(StorageKind.FileContent, (ulong)bytes.Length - offset, false, true) : new(StorageKind.Unmapped, 0, false, false);
    public bool IsExecutable(ulong offset, ulong length = 1) => false;
    public bool IsWritable(ulong offset, ulong length = 1) => Query(offset).AvailableBytes >= length;
    public void ReadBytes(ulong offset, Span<byte> destination) => bytes.AsSpan(checked((int)offset), destination.Length).CopyTo(destination);
    public ulong ReadUnsigned(ulong offset, int width)
    {
        ulong value = 0;
        for (var i = 0; i < width; i++) value |= (ulong)bytes[checked((int)offset + i)] << (i * 8);
        return value;
    }
    public PointerTarget ReadPointer(ulong offset) => Pointers.GetValueOrDefault(offset) ?? (ReadUnsigned(offset, PointerWidth) == 0 ? new PointerTarget.Null() : new PointerTarget.NotPointer("无重定位"));
    internal void Put(ulong offset, ulong value, int width)
    {
        for (var i = 0; i < width; i++) bytes[checked((int)offset + i)] = (byte)(value >> (i * 8));
    }
}
