using System.Buffers.Binary;
using System.Security.Cryptography;

namespace Cpp2CS.Native;

public sealed class ElfImage
{
    private readonly byte[] bytes;
    private readonly List<(ulong Address, ulong Offset, ulong FileSize, ulong MemorySize, uint Flags)> segments = [];
    private readonly Dictionary<ulong, (uint Kind, ulong Value)> relocations = [];
    private readonly Dictionary<string, ulong> sections = [];
    public string Sha256 { get; }
    public ElfImage(string path)
    {
        bytes = File.ReadAllBytes(path);
        Sha256 = Convert.ToHexString(SHA256.HashData(bytes)).ToLowerInvariant();
        if (bytes.Length < 64 || !bytes.AsSpan(0, 4).SequenceEqual(new byte[] { 127, 69, 76, 70 }) || bytes[4] != 2 || bytes[5] != 1 || U16(18) != 183)
            throw new InvalidDataException("需要 AArch64 ELF64 little-endian");
        var phoff = U64(32);
        for (var i = 0; i < U16(56); i++)
        {
            var p = checked((int)(phoff + (ulong)(i * U16(54))));
            if (U32(p) == 1) segments.Add((U64(p + 16), U64(p + 8), U64(p + 32), U64(p + 40), U32(p + 4)));
        }
        var shoff = U64(40);
        var stringsHeader = checked((int)(shoff + (ulong)(U16(62) * U16(58))));
        var stringsOffset = U64(stringsHeader + 24);
        for (var i = 0; i < U16(60); i++)
        {
            var s = checked((int)(shoff + (ulong)(i * U16(58))));
            var nameStart = checked((int)(stringsOffset + U32(s)));
            var nameEnd = Array.IndexOf(bytes, (byte)0, nameStart);
            sections[System.Text.Encoding.ASCII.GetString(bytes, nameStart, nameEnd - nameStart)] = U64(s + 16);
            if (U32(s + 4) != 4) continue;
            var offset = U64(s + 24);
            var size = U64(s + 32);
            if (U64(s + 56) != 24 || size % 24 != 0) throw new InvalidDataException("无效 RELA 表");
            for (ulong n = 0; n < size; n += 24)
            {
                var r = checked((int)(offset + n));
                var kind = (uint)U64(r + 8);
                var value = U64(r + 16);
                if (!relocations.TryAdd(U64(r), (kind, value)) && relocations[U64(r)] != (kind, value))
                    throw new InvalidDataException("冲突的重定位");
            }
        }
    }
    public ulong? SectionAddress(string name) => sections.TryGetValue(name, out var address) ? address : null;
    public byte[] Read(ulong address, int size)
    {
        foreach (var s in segments)
            if (address >= s.Address && address - s.Address <= s.FileSize && (ulong)size <= s.FileSize - (address - s.Address))
                return bytes.AsSpan(checked((int)(s.Offset + address - s.Address)), size).ToArray();
        throw new InvalidDataException($"地址未映射到文件：0x{address:x}+{size}");
    }
    public bool IsExecutable(ulong address) => segments.Any(s => (s.Flags & 1) != 0 && address >= s.Address && address - s.Address < s.FileSize);
    public ulong? ReadImmutableScalar(ulong address, int size)
    {
        if (size is not (1 or 2 or 4 or 8) || !segments.Any(s => (s.Flags & 6) == 4 && address >= s.Address &&
            address - s.Address <= s.FileSize && (ulong)size <= s.FileSize - (address - s.Address)) ||
            relocations.Keys.Any(r => r < address + (ulong)size && r + 8 > address)) return null;
        return Read(address, size).Select((b, i) => (ulong)b << (i * 8)).Aggregate(0UL, (a, b) => a | b);
    }
    public bool IsWritable(ulong address) => segments.Any(s => (s.Flags & 2) != 0 && address >= s.Address && address - s.Address < s.MemorySize);
    public bool TryRelativePointer(ulong address, out ulong value)
    {
        value = 0;
        if (!relocations.TryGetValue(address, out var entry) || entry.Kind != 1027) return false;
        value = entry.Value;
        return true;
    }
    public ulong ReadResolvedPointer(ulong address)
    {
        if (!relocations.TryGetValue(address, out var relocation)) return BinaryPrimitives.ReadUInt64LittleEndian(Read(address, 8));
        if (relocation.Kind != 1027) throw new InvalidDataException($"指针 0x{address:x} 的重定位类型 {relocation.Kind} 尚未解析");
        return relocation.Value;
    }
    public string ReadCString(ulong address, int limit = 256)
    {
        var value = Read(address, limit);
        var end = Array.IndexOf(value, (byte)0);
        return end < 0 ? "" : System.Text.Encoding.UTF8.GetString(value, 0, end);
    }
    private ushort U16(int p) => BinaryPrimitives.ReadUInt16LittleEndian(bytes.AsSpan(p, 2));
    private uint U32(int p) => BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(p, 4));
    private ulong U64(int p) => BinaryPrimitives.ReadUInt64LittleEndian(bytes.AsSpan(p, 8));
}
