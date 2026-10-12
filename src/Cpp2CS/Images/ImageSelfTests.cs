using System.Buffers.Binary;

namespace Cpp2CS.Images;

public static class ImageSelfTests
{
    public static int Run()
    {
        var checks = 0;
        var elf = ImageDocument.Parse(ElfWithRelr());
        Check(elf.Architecture == Architecture.Arm64 && elf.PreferredBase == 0x1000, ref checks);
        Check(elf.Resolve(0x0fff).Kind == AddressKind.Unmapped, ref checks);
        Check(elf.Resolve(0x1000) is { Kind: AddressKind.FileBacked, FileOffset: 0x100, AvailableBytes: 0x40 }, ref checks);
        Check(elf.Resolve(0x103f) is { Kind: AddressKind.FileBacked, FileOffset: 0x13f, AvailableBytes: 1 }, ref checks);
        Check(elf.Resolve(0x1040) is { Kind: AddressKind.ZeroFill, FileOffset: null, AvailableBytes: 0x40 }, ref checks);
        Check(elf.Resolve(0x107f) is { Kind: AddressKind.ZeroFill, AvailableBytes: 1 }, ref checks);
        Check(elf.Resolve(0x1080).Kind == AddressKind.Unmapped && elf.Resolve(ulong.MaxValue).Kind == AddressKind.Unmapped, ref checks);
        Check(elf.RelocationTables.Single().Records == 2 && elf.RelocationTables.Single().Fixups == 3, ref checks);
        Check(elf.CodeRelocations.Select(r => r.Address).SequenceEqual(new ulong[] { 0x1000, 0x1008, 0x1018 }), ref checks);
        Check(elf.HasCodeRelocation(0x1007, 1) && !elf.HasCodeRelocation(0x1010, 8) && elf.HasCodeRelocation(0x1017, 2), ref checks);
        var pe = ImageDocument.Parse(PeWithFixup(0x300));
        const ulong imageBase = 0x180000000;
        Check(pe.Architecture == Architecture.X64 && pe.PreferredBase == imageBase, ref checks);
        Check(pe.Resolve(imageBase + 0x1000) is { Kind: AddressKind.FileBacked, FileOffset: 0x200, AvailableBytes: 0x200 }, ref checks);
        Check(pe.Resolve(imageBase + 0x1200) is { Kind: AddressKind.ZeroFill, AvailableBytes: 0x100 }, ref checks);
        Check(pe.Resolve(imageBase + 0x12ff) is { Kind: AddressKind.ZeroFill, AvailableBytes: 1 } && pe.Resolve(imageBase + 0x1300).Kind == AddressKind.Unmapped, ref checks);
        Check(pe.RelocationTables.Single().Records == 2 && pe.RelocationTables.Single().Fixups == 1, ref checks);
        Check(pe.CodeRelocations.Single().Address == imageBase + 0x1010 && pe.HasCodeRelocation(imageBase + 0x1017, 1), ref checks);
        var padded = ImageDocument.Parse(PeWithFixup(0x180));
        Check(padded.ExecutableRanges.Single() is { FileSize: 0x180, MemorySize: 0x180 }, ref checks);
        Check(padded.Resolve(imageBase + 0x117f).Kind == AddressKind.FileBacked && padded.Resolve(imageBase + 0x1180).Kind == AddressKind.Unmapped, ref checks);
        return checks;
    }

    private static void Check(bool condition, ref int checks)
    {
        if (!condition) throw new InvalidDataException($"Image self-check {checks + 1} failed");
        checks++;
    }

    private static byte[] ElfWithRelr()
    {
        var bytes = new byte[0x280];
        U32(bytes, 0, 0x464c457f); bytes[4] = 2; bytes[5] = 1; bytes[6] = 1;
        U16(bytes, 16, 3); U16(bytes, 18, 183); U32(bytes, 20, 1);
        U64(bytes, 32, 64); U64(bytes, 40, 0x200); U16(bytes, 52, 64);
        U16(bytes, 54, 56); U16(bytes, 56, 1); U16(bytes, 58, 64); U16(bytes, 60, 2);
        U32(bytes, 64, 1); U32(bytes, 68, 5); U64(bytes, 72, 0x100); U64(bytes, 80, 0x1000);
        U64(bytes, 96, 0x40); U64(bytes, 104, 0x80); U64(bytes, 112, 1);
        U64(bytes, 0x180, 0x1000); U64(bytes, 0x188, 0b1011);
        U32(bytes, 0x244, 19); U64(bytes, 0x258, 0x180); U64(bytes, 0x260, 16); U64(bytes, 0x278, 8);
        return bytes;
    }

    private static byte[] PeWithFixup(uint virtualSize)
    {
        var bytes = new byte[0x400];
        U16(bytes, 0, 0x5a4d); U32(bytes, 60, 0x80); U32(bytes, 0x80, 0x4550);
        U16(bytes, 0x84, 0x8664); U16(bytes, 0x86, 1); U16(bytes, 0x94, 240);
        const int optional = 0x98;
        U16(bytes, optional, 0x20b); U64(bytes, optional + 24, 0x180000000);
        U32(bytes, optional + 32, 0x1000); U32(bytes, optional + 36, 0x200);
        U32(bytes, optional + 56, 0x2000); U32(bytes, optional + 60, 0x200); U32(bytes, optional + 108, 16);
        U32(bytes, optional + 112 + 5 * 8, 0x1100); U32(bytes, optional + 116 + 5 * 8, 12);
        const int section = optional + 240;
        ".text"u8.CopyTo(bytes.AsSpan(section));
        U32(bytes, section + 8, virtualSize); U32(bytes, section + 12, 0x1000);
        U32(bytes, section + 16, 0x200); U32(bytes, section + 20, 0x200); U32(bytes, section + 36, 0x60000020);
        U32(bytes, 0x300, 0x1000); U32(bytes, 0x304, 12); U16(bytes, 0x308, 0xa010);
        return bytes;
    }

    private static void U16(byte[] bytes, int offset, ushort value) => BinaryPrimitives.WriteUInt16LittleEndian(bytes.AsSpan(offset, 2), value);
    private static void U32(byte[] bytes, int offset, uint value) => BinaryPrimitives.WriteUInt32LittleEndian(bytes.AsSpan(offset, 4), value);
    private static void U64(byte[] bytes, int offset, ulong value) => BinaryPrimitives.WriteUInt64LittleEndian(bytes.AsSpan(offset, 8), value);
}
