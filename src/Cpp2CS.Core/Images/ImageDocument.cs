using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;

namespace Cpp2CS.Images;

public sealed record ImageRange(string Name, ulong Address, long FileOffset, ulong FileSize, ulong MemorySize, bool Executable);
public enum AddressKind { FileBacked, ZeroFill, Unmapped }
public sealed record AddressResolution(AddressKind Kind, ImageRange? Range, long? FileOffset, ulong AvailableBytes);
public sealed record CodeRelocation(ulong Address, int Size, string Kind, long RecordFileOffset);
/// <summary>节头表中的一节。Flags 为 ELF sh_flags（2 SHF_ALLOC，4 SHF_EXECINSTR）；PE 节以可执行位换算。</summary>
public sealed record ImageSection(string Name, ulong Address, ulong Size, uint Type, ulong Flags)
{
    public bool Executable => (Flags & 4) != 0;
    public bool Contains(ulong address) => address >= Address && address - Address < Size;
}
public sealed record RelocationTableSummary(string Name, string Format, long FileOffset, ulong Size, long Records, long Fixups, IReadOnlyDictionary<string, long> Kinds);

public sealed class ImageDocument
{
    private readonly byte[] bytes;
    public ReadOnlyMemory<byte> Bytes => bytes;
    public string Sha256 { get; }
    public Architecture Architecture { get; }
    public ulong PreferredBase { get; }
    public IReadOnlyList<ImageRange> Ranges { get; }
    public IReadOnlyList<ImageRange> ExecutableRanges { get; }
    public IReadOnlyList<RelocationTableSummary> RelocationTables { get; }
    public IReadOnlyList<CodeRelocation> CodeRelocations { get; }
    private readonly int maximumRelocationSize;

    /// <summary>ELF PT_GNU_EH_FRAME 指向的 .eh_frame_hdr 虚拟地址。</summary>
    public ulong? EhFrameHeader { get; private init; }

    /// <summary>PE 异常目录（.pdata）的虚拟地址与长度。</summary>
    public (ulong Address, ulong Size)? ExceptionDirectory { get; private init; }

    private IReadOnlyDictionary<ulong, ulong> pointerFixups = new Dictionary<ulong, ulong>();

    /// <summary>加载器重定位记录明确指定的指针；不把文件中的任意整数当作地址。</summary>
    public ulong? RelocatedPointer(ulong address) => pointerFixups.TryGetValue(address, out var target) ? target : null;

    /// <summary>重定位记录给出的全部指针值（可能重复）。</summary>
    public IEnumerable<ulong> RelocatedPointerTargets() => pointerFixups.Values;

    /// <summary>重定位指针：(指针所在地址, 指针值)。</summary>
    public IEnumerable<KeyValuePair<ulong, ulong>> RelocatedPointers => pointerFixups;

    /// <summary>引用未定义动态符号的指针位置（GOT、JUMP_SLOT）及符号名。</summary>
    public IReadOnlyDictionary<ulong, string> Imports { get; private init; } = new Dictionary<ulong, string>();

    /// <summary>ELF DT_NEEDED 中声明的动态库名，不从导入符号名推测库名。</summary>
    public IReadOnlyList<string> NeededLibraries { get; private init; } = [];

    /// <summary>按符号重定位的指针位置及符号名，含已定义符号（如静态链接并导出的 libc++abi 经 PLT 引用）。</summary>
    public IReadOnlyDictionary<ulong, string> SymbolSlots { get; private init; } = new Dictionary<ulong, string>();

    /// <summary>有地址的节（ELF SHF_ALLOC 节、PE 节），按地址升序。</summary>
    public IReadOnlyList<ImageSection> Sections { get; private init; } = [];

    public ImageSection? Section(string name) => Sections.FirstOrDefault(s => s.Name == name);

    public ImageSection? SectionAt(ulong address) => Sections.FirstOrDefault(s => s.Contains(address));

    /// <summary>ELF 加载器完成重定位后保护为只读的范围。</summary>
    public IReadOnlyList<(ulong Address, ulong Size)> RelroRanges { get; private init; } = [];

    /// <summary>导出符号：ELF 动态符号表中已定义的函数，PE 导出表中的名称导出。</summary>
    public IReadOnlyDictionary<string, ulong> Exports { get; private init; } = new Dictionary<string, ulong>();

    private ImageDocument(byte[] bytes, Architecture architecture, ulong preferredBase, List<ImageRange> ranges,
        List<RelocationTableSummary> tables, List<CodeRelocation> codeRelocations)
    {
        this.bytes = bytes;
        Sha256 = Convert.ToHexString(SHA256.HashData(bytes));
        Architecture = architecture;
        PreferredBase = preferredBase;
        Ranges = ranges.OrderBy(r => r.Address).ToArray();
        ExecutableRanges = Ranges.Where(r => r.Executable).ToArray();
        RelocationTables = tables.ToArray();
        CodeRelocations = codeRelocations.OrderBy(r => r.Address).ToArray();
        maximumRelocationSize = codeRelocations.Count == 0 ? 0 : CodeRelocations.Max(r => r.Size);
    }

    public static ImageDocument Load(string path) => Parse(File.ReadAllBytes(path));

    internal static ImageDocument Parse(byte[] bytes)
    {
        var reader = new ImageReader(bytes);
        if (reader.U32(0) == 0x464c457f) return LoadElf(reader);
        if (reader.U16(0) == 0x5a4d) return LoadPe(reader);
        throw new InvalidDataException("需要 ELF64 AArch64 或 PE32+ AMD64 文件");
    }

    public AddressResolution Resolve(ulong address)
    {
        var low = 0;
        var high = Ranges.Count - 1;
        while (low <= high)
        {
            var middle = low + (high - low) / 2;
            var range = Ranges[middle];
            if (address < range.Address) { high = middle - 1; continue; }
            var delta = address - range.Address;
            if (delta >= range.MemorySize) { low = middle + 1; continue; }
            if (delta < range.FileSize)
                return new(AddressKind.FileBacked, range, checked(range.FileOffset + (long)delta), range.FileSize - delta);
            return new(AddressKind.ZeroFill, range, null, range.MemorySize - delta);
        }
        return new(AddressKind.Unmapped, null, null, 0);
    }

    public bool IsExecutable(ulong address)
    {
        var mapping = Resolve(address);
        return mapping.Kind == AddressKind.FileBacked && mapping.Range!.Executable;
    }

    /// <summary>读取文件中实际存在的字节；未映射或越过文件内容时抛出。</summary>
    public ReadOnlySpan<byte> Read(ulong address, int size)
    {
        var mapping = Resolve(address);
        if (mapping.Kind != AddressKind.FileBacked || (ulong)size > mapping.AvailableBytes)
            throw new InvalidDataException($"地址未完整映射到文件：0x{address:X}+{size}");
        return bytes.AsSpan(checked((int)mapping.FileOffset!.Value), size);
    }

    /// <summary>读取至多 size 个文件字节；遇到映射末尾时截短，未映射时为空。</summary>
    public ReadOnlySpan<byte> ReadUpTo(ulong address, int size)
    {
        var mapping = Resolve(address);
        if (mapping.Kind != AddressKind.FileBacked) return [];
        var available = (int)Math.Min((ulong)size, mapping.AvailableBytes);
        return bytes.AsSpan(checked((int)mapping.FileOffset!.Value), available);
    }

    /// <summary>
    /// 读取加载后（按首选基址）的指针值：应用 ELF RELATIVE/符号重定位，零填充区为 0。
    /// 引用外部符号的位置返回 null，名称见 <see cref="Imports"/>；未映射地址抛出。
    /// </summary>
    public ulong? ReadPointer(ulong address)
    {
        if (pointerFixups.TryGetValue(address, out var value)) return value;
        if (Imports.ContainsKey(address)) return null;
        var mapping = Resolve(address);
        if (mapping.Kind == AddressKind.ZeroFill) return 0;
        return ReadU64(address);
    }

    public uint ReadU32(ulong address) => BinaryPrimitives.ReadUInt32LittleEndian(Read(address, 4));
    public ulong ReadU64(ulong address) => BinaryPrimitives.ReadUInt64LittleEndian(Read(address, 8));
    public int ReadI32(ulong address) => BinaryPrimitives.ReadInt32LittleEndian(Read(address, 4));

    public bool HasCodeRelocation(ulong address, int size)
    {
        if (size <= 0) throw new ArgumentOutOfRangeException(nameof(size));
        var end = checked(address + (ulong)size);
        var earliest = address >= (ulong)maximumRelocationSize ? address - (ulong)maximumRelocationSize : 0;
        var low = 0;
        var high = CodeRelocations.Count;
        while (low < high)
        {
            var middle = low + (high - low) / 2;
            if (CodeRelocations[middle].Address < earliest) low = middle + 1;
            else high = middle;
        }
        for (var i = low; i < CodeRelocations.Count && CodeRelocations[i].Address < end; i++)
            if (checked(CodeRelocations[i].Address + (ulong)CodeRelocations[i].Size) > address) return true;
        return false;
    }

    private static void ValidateRanges(ImageReader reader, List<ImageRange> ranges)
    {
        ImageRange? previous = null;
        foreach (var range in ranges.OrderBy(r => r.Address))
        {
            if (range.MemorySize == 0) throw new InvalidDataException("空映射不得进入地址表");
            if (range.FileSize > range.MemorySize) throw new InvalidDataException("文件映射超过内存范围");
            _ = checked(range.Address + range.MemorySize);
            reader.Require(range.FileOffset, range.FileSize);
            if (previous is not null && previous.Address + previous.MemorySize > range.Address)
                throw new InvalidDataException("虚拟地址映射重叠");
            previous = range;
        }
    }

    private static long MapFile(List<ImageRange> ranges, ulong address, ulong size)
    {
        if (size == 0) throw new InvalidDataException("映射查询长度不能为零");
        _ = checked(address + size);
        foreach (var range in ranges)
            if (address >= range.Address && address - range.Address < range.FileSize && size <= range.FileSize - (address - range.Address))
                return checked(range.FileOffset + (long)(address - range.Address));
        throw new InvalidDataException($"范围未完整映射到文件：0x{address:X}+0x{size:X}");
    }

    private static ImageDocument LoadElf(ImageReader reader)
    {
        reader.Require(0, 64);
        if (reader.Byte(4) != 2 || reader.Byte(5) != 1 || reader.Byte(6) != 1 || reader.U16(18) != 183 ||
            reader.U32(20) != 1 || reader.U16(16) is not (2 or 3) || reader.U16(52) != 64)
            throw new InvalidDataException("需要 little-endian ELF64 AArch64 ET_EXEC/ET_DYN");
        var phoff = reader.Offset(reader.U64(32));
        var shoff = reader.Offset(reader.U64(40));
        var phsize = reader.U16(54);
        var shsize = reader.U16(58);
        uint phcount = reader.U16(56);
        ulong shcount = reader.U16(60);
        uint stringIndex = reader.U16(62);
        if (shoff != 0)
        {
            if (shsize != 64) throw new InvalidDataException("ELF section header 大小错误");
            reader.Require(shoff, 64);
            if (shcount == 0) shcount = reader.U64(shoff + 32);
            if (phcount == 0xffff) phcount = reader.U32(shoff + 44);
            if (stringIndex == 0xffff) stringIndex = reader.U32(shoff + 40);
            reader.Require(shoff, checked(shcount * 64));
        }
        else if (shcount != 0 || phcount == 0xffff || stringIndex != 0)
            throw new InvalidDataException("缺少 ELF 扩展编号所需 section table");
        if (phsize != 56 || phcount == 0) throw new InvalidDataException("ELF program header 不完整");
        reader.Require(phoff, checked((ulong)phcount * 56));
        var ranges = new List<ImageRange>();
        var dynamicRanges = new List<(long Offset, ulong Size)>();
        var relroRanges = new List<(ulong Address, ulong Size)>();
        ulong? ehFrameHeader = null;
        for (uint i = 0; i < phcount; i++)
        {
            var p = checked(phoff + i * 56L);
            var type = reader.U32(p);
            var offset = reader.Offset(reader.U64(p + 8));
            var address = reader.U64(p + 16);
            var fileSize = reader.U64(p + 32);
            var memorySize = reader.U64(p + 40);
            if (type == 1 && fileSize > memorySize) throw new InvalidDataException("ELF LOAD 文件长度超过内存长度");
            if (type == 1 && memorySize != 0)
            {
                var alignment = reader.U64(p + 48);
                if (alignment > 1 && ((alignment & (alignment - 1)) != 0 || address % alignment != (ulong)offset % alignment))
                    throw new InvalidDataException("ELF LOAD 对齐不一致");
                ranges.Add(new($"LOAD[{i}]", address, offset, fileSize, memorySize, (reader.U32(p + 4) & 1) != 0));
            }
            if (type == 2 && fileSize != 0) dynamicRanges.Add((offset, fileSize));
            if (type == 0x6474e552 && memorySize != 0) relroRanges.Add((address, memorySize));
            if (type == 0x6474e550 && memorySize != 0)
            {
                if (ehFrameHeader is not null) throw new InvalidDataException("ELF 有多个 PT_GNU_EH_FRAME");
                ehFrameHeader = address;
            }
        }
        if (ranges.Count == 0) throw new InvalidDataException("ELF 没有 LOAD 映射");
        ValidateRanges(reader, ranges);
        var collector = new RelocationCollector(reader, ranges);
        long stringsOffset = 0;
        ulong stringsSize = 0;
        if (stringIndex != 0)
        {
            if (stringIndex >= shcount) throw new InvalidDataException("ELF section name table 索引越界");
            var s = checked(shoff + stringIndex * 64L);
            stringsOffset = reader.Offset(reader.U64(s + 24));
            stringsSize = reader.U64(s + 32);
            reader.Require(stringsOffset, stringsSize);
        }
        var exports = new Dictionary<string, ulong>(StringComparer.Ordinal);
        var symbols = new List<(string Name, ulong Value, bool Defined)>();
        var sections = new List<ImageSection>();
        for (ulong i = 0; i < shcount; i++)
        {
            var s = checked(shoff + (long)i * 64);
            var type = reader.U32(s + 4);
            var sectionFlags = reader.U64(s + 8);
            if ((sectionFlags & 2) != 0 && reader.U64(s + 32) != 0 && stringsSize != 0)
                sections.Add(new(reader.String(stringsOffset, stringsSize, reader.U32(s)), reader.U64(s + 16), reader.U64(s + 32), type, sectionFlags));
            if (type == 11)
            {
                if (symbols.Count != 0) throw new InvalidDataException("ELF 有多个动态符号表");
                ReadElfSymbols(reader, shoff, shcount, s, exports, symbols);
            }
            if (type is 0x60000001 or 0x60000002) throw new NotSupportedException("暂不支持 Android packed relocation section");
            if (type is not (4 or 9 or 19)) continue;
            var name = stringsSize == 0 ? $"section[{i}]" : reader.String(stringsOffset, stringsSize, reader.U32(s));
            var format = type == 4 ? "RELA" : type == 9 ? "REL" : "RELR";
            var stride = type == 4 ? 24UL : type == 9 ? 16UL : 8UL;
            if (reader.U64(s + 56) != stride) throw new InvalidDataException($"{name} relocation entry 大小错误");
            collector.Add(name, format, reader.Offset(reader.U64(s + 24)), reader.U64(s + 32), stride);
        }
        var neededLibraries = new List<string>();
        foreach (var (offset, size) in dynamicRanges)
        {
            reader.Require(offset, size);
            if (size % 16 != 0) throw new InvalidDataException("ELF dynamic table 长度错误");
            var tags = new Dictionary<long, ulong>();
            var needed = new List<ulong>();
            var terminated = false;
            for (ulong i = 0; i < size; i += 16)
            {
                var p = checked(offset + (long)i);
                var tag = reader.I64(p);
                if (tag == 0) { terminated = true; break; }
                if (tag == 1) needed.Add(reader.U64(p + 8));
                if (tag is 2 or 5 or 7 or 8 or 9 or 10 or 17 or 18 or 19 or 20 or 23 or 35 or 36 or 37 or 0x6000000f or 0x60000011 or 0x6fffe000 or 0x6fffe001 or 0x6fffe003)
                {
                    var value = reader.U64(p + 8);
                    if (!tags.TryAdd(tag, value) && tags[tag] != value) throw new InvalidDataException("重复 ELF dynamic relocation tag 不一致");
                }
            }
            if (!terminated) throw new InvalidDataException("ELF dynamic table 缺少 DT_NULL");
            if (needed.Count > 0)
            {
                if (!tags.TryGetValue(5, out var stringAddress) || !tags.TryGetValue(10, out var stringSize))
                    throw new InvalidDataException("ELF DT_NEEDED 缺少动态字符串表");
                var stringOffset = MapFile(ranges, stringAddress, stringSize);
                neededLibraries.AddRange(needed.Select(n => reader.String(stringOffset, stringSize, checked((uint)n))));
            }
            if (tags.ContainsKey(0x6000000f) || tags.ContainsKey(0x60000011)) throw new NotSupportedException("暂不支持 Android packed REL/RELA，不能确认代码重定位覆盖");
            AddDynamicTable(collector, ranges, tags, "DT_RELA", 7, 8, 9, "RELA", 24);
            AddDynamicTable(collector, ranges, tags, "DT_REL", 17, 18, 19, "REL", 16);
            AddDynamicTable(collector, ranges, tags, "DT_RELR", 36, 35, 37, "RELR", 8);
            AddDynamicTable(collector, ranges, tags, "DT_ANDROID_RELR", 0x6fffe000, 0x6fffe001, 0x6fffe003, "RELR", 8);
            if (tags.TryGetValue(23, out var plt))
            {
                if (!tags.TryGetValue(2, out var pltSize) || !tags.TryGetValue(20, out var kind) || kind is not (7 or 17))
                    throw new InvalidDataException("ELF PLT relocation tags 不完整");
                if (pltSize != 0) collector.Add("DT_JMPREL", kind == 7 ? "RELA" : "REL", MapFile(ranges, plt, pltSize), pltSize, kind == 7 ? 24UL : 16UL);
            }
            else if (tags.GetValueOrDefault(2) != 0) throw new InvalidDataException("缺少 DT_JMPREL");
        }
        collector.ScanElf();
        var fixups = collector.Pointers;
        var imports = new Dictionary<ulong, string>();
        var slots = new Dictionary<ulong, string>();
        foreach (var (address, (symbol, addend)) in collector.SymbolPointers)
        {
            if (symbol >= symbols.Count) throw new InvalidDataException($"重定位符号索引越界：{symbol}");
            var entry = symbols[(int)symbol];
            if (entry.Name.Length > 0) slots[address] = entry.Name;
            if (entry.Defined) fixups[address] = unchecked(entry.Value + (ulong)addend);
            else imports[address] = entry.Name;
        }
        return new(reader.Bytes, Architecture.Arm64, ranges.Min(r => r.Address), ranges, collector.Summaries, collector.CodeRelocations)
        {
            EhFrameHeader = ehFrameHeader,
            RelroRanges = relroRanges,
            Sections = sections.OrderBy(x => x.Address).ToArray(),
            Exports = exports,
            Imports = imports,
            NeededLibraries = neededLibraries.Distinct(StringComparer.Ordinal).ToArray(),
            SymbolSlots = slots,
            pointerFixups = fixups,
        };
    }

    // SHT_DYNSYM：symbols 按索引保存全部条目供重定位解析；exports 只收集已定义（st_shndx != 0）的 STT_FUNC 符号。
    private static void ReadElfSymbols(ImageReader reader, long shoff, ulong shcount, long section, Dictionary<string, ulong> exports,
        List<(string Name, ulong Value, bool Defined)> symbols)
    {
        if (reader.U64(section + 56) != 24) throw new InvalidDataException("ELF 符号表 entry 大小错误");
        var link = reader.U32(section + 40);
        if (link >= shcount) throw new InvalidDataException("ELF 符号表字符串表索引越界");
        var strings = checked(shoff + link * 64L);
        var stringsOffset = reader.Offset(reader.U64(strings + 24));
        var stringsSize = reader.U64(strings + 32);
        var offset = reader.Offset(reader.U64(section + 24));
        var size = reader.U64(section + 32);
        reader.Require(offset, size);
        symbols.Add(("", 0, false));
        for (ulong n = 24; n < size; n += 24)
        {
            var p = checked(offset + (long)n);
            var info = reader.Byte(p + 4);
            var index = reader.U16(p + 6);
            var value = reader.U64(p + 8);
            var name = reader.String(stringsOffset, stringsSize, reader.U32(p));
            symbols.Add((name, value, index != 0));
            if ((info & 0xf) != 2 || index == 0 || value == 0) continue;
            if (!exports.TryAdd(name, value) && exports[name] != value)
                throw new InvalidDataException($"ELF 导出符号 {name} 地址冲突");
        }
    }

    private static void AddDynamicTable(RelocationCollector collector, List<ImageRange> ranges, Dictionary<long, ulong> tags,
        string name, long addressTag, long sizeTag, long entryTag, string format, ulong stride)
    {
        if (!tags.TryGetValue(addressTag, out var address))
        {
            if (tags.GetValueOrDefault(sizeTag) != 0) throw new InvalidDataException($"缺少 {name} 地址");
            return;
        }
        if (!tags.TryGetValue(sizeTag, out var size) || !tags.TryGetValue(entryTag, out var entrySize) || entrySize != stride)
            throw new InvalidDataException($"{name} 长度或 entry 大小错误");
        if (size != 0) collector.Add(name, format, MapFile(ranges, address, size), size, stride);
    }

    private static ImageDocument LoadPe(ImageReader reader)
    {
        reader.Require(0, 64);
        var pe = (long)reader.U32(60);
        reader.Require(pe, 24);
        if (pe < 64 || reader.U32(pe) != 0x4550 || reader.U16(pe + 4) != 0x8664) throw new InvalidDataException("需要 PE AMD64 文件");
        var count = reader.U16(pe + 6);
        var optionalSize = reader.U16(pe + 20);
        var optional = checked(pe + 24);
        reader.Require(optional, optionalSize);
        if (optionalSize < 112 || reader.U16(optional) != 0x20b || count == 0) throw new InvalidDataException("需要 PE32+ optional header");
        var imageBase = reader.U64(optional + 24);
        var imageSize = reader.U32(optional + 56);
        var headersSize = reader.U32(optional + 60);
        var sectionAlignment = reader.U32(optional + 32);
        var fileAlignment = reader.U32(optional + 36);
        if (imageSize == 0 || headersSize == 0 || headersSize > imageSize ||
            sectionAlignment == 0 || (sectionAlignment & (sectionAlignment - 1)) != 0 ||
            fileAlignment == 0 || (fileAlignment & (fileAlignment - 1)) != 0 || sectionAlignment < fileAlignment)
            throw new InvalidDataException("PE 映像大小或对齐错误");
        _ = checked(imageBase + imageSize);
        var ranges = new List<ImageRange> { new("Headers", imageBase, 0, headersSize, headersSize, false) };
        var sectionTable = checked(optional + optionalSize);
        reader.Require(sectionTable, checked((ulong)count * 40));
        if ((ulong)(sectionTable + count * 40L) > headersSize) throw new InvalidDataException("PE section table 超过 SizeOfHeaders");
        for (var i = 0; i < count; i++)
        {
            var s = checked(sectionTable + i * 40L);
            var name = Encoding.ASCII.GetString(reader.Span(s, 8)).TrimEnd('\0');
            var virtualSize = reader.U32(s + 8);
            var rva = reader.U32(s + 12);
            var rawSize = reader.U32(s + 16);
            var rawOffset = reader.U32(s + 20);
            var memorySize = virtualSize == 0 ? rawSize : virtualSize;
            reader.Require(rawOffset, rawSize);
            if (memorySize == 0) continue;
            if (rva % sectionAlignment != 0 || (rawSize != 0 && rawOffset % fileAlignment != 0) || (ulong)rva + memorySize > imageSize)
                throw new InvalidDataException($"PE section {name} 范围或对齐错误");
            ranges.Add(new(name, checked(imageBase + rva), rawOffset, Math.Min(rawSize, memorySize), memorySize, (reader.U32(s + 36) & 0x20000000) != 0));
        }
        ValidateRanges(reader, ranges);
        var directoryCount = reader.U32(optional + 108);
        if ((ulong)optionalSize < 112UL + directoryCount * 8UL) throw new InvalidDataException("PE data directory 越界");
        var collector = new RelocationCollector(reader, ranges);
        if (directoryCount > 5)
        {
            var rva = reader.U32(optional + 112 + 5 * 8);
            var size = reader.U32(optional + 116 + 5 * 8);
            if ((rva == 0) != (size == 0)) throw new InvalidDataException("PE base relocation 地址/长度不一致");
            if (size != 0) collector.ScanPe(MapFile(ranges, checked(imageBase + rva), size), size, imageBase);
        }
        (ulong, ulong)? exceptionDirectory = null;
        if (directoryCount > 3 && reader.U32(optional + 112 + 3 * 8) is var exceptionRva and not 0)
            exceptionDirectory = (checked(imageBase + exceptionRva), reader.U32(optional + 116 + 3 * 8));
        var exports = new Dictionary<string, ulong>(StringComparer.Ordinal);
        if (directoryCount > 0 && reader.U32(optional + 112) is var exportRva and not 0)
            ReadPeExports(reader, ranges, imageBase, exportRva, exports);
        return new(reader.Bytes, Architecture.X64, imageBase, ranges, collector.Summaries, collector.CodeRelocations)
        {
            ExceptionDirectory = exceptionDirectory,
            Sections = ranges.Skip(1).Select(r => new ImageSection(r.Name, r.Address, r.MemorySize, 0, 2UL | (r.Executable ? 4UL : 0))).ToArray(),
            Exports = exports,
        };
    }

    private static void ReadPeExports(ImageReader reader, List<ImageRange> ranges, ulong imageBase, uint rva, Dictionary<string, ulong> exports)
    {
        long Map(ulong r, ulong size) => MapFile(ranges, checked(imageBase + r), size);
        var directory = Map(rva, 40);
        var functionCount = reader.U32(directory + 20);
        var nameCount = reader.U32(directory + 24);
        if (nameCount == 0) return;
        var functions = Map(reader.U32(directory + 28), checked(functionCount * 4UL));
        var names = Map(reader.U32(directory + 32), checked(nameCount * 4UL));
        var ordinals = Map(reader.U32(directory + 36), checked(nameCount * 2UL));
        for (uint i = 0; i < nameCount; i++)
        {
            var ordinal = reader.U16(ordinals + i * 2L);
            if (ordinal >= functionCount) throw new InvalidDataException("PE 导出序号越界");
            var nameOffset = Map(reader.U32(names + i * 4L), 1);
            var end = Array.IndexOf(reader.Bytes, (byte)0, checked((int)nameOffset));
            if (end < 0) throw new InvalidDataException("PE 导出名称未终止");
            var name = Encoding.ASCII.GetString(reader.Bytes, (int)nameOffset, end - (int)nameOffset);
            var target = reader.U32(functions + ordinal * 4L);
            if (target == 0) continue;
            if (!exports.TryAdd(name, checked(imageBase + target)))
                throw new InvalidDataException($"PE 导出名称 {name} 重复");
        }
    }
}

internal sealed class ImageReader(byte[] bytes)
{
    public byte[] Bytes { get; } = bytes;
    public void Require(long offset, ulong size)
    {
        if (offset < 0 || (ulong)offset > (ulong)Bytes.LongLength || size > (ulong)Bytes.LongLength - (ulong)offset)
            throw new InvalidDataException($"文件范围越界：0x{offset:X}+0x{size:X}");
    }
    public long Offset(ulong value) => value <= long.MaxValue ? (long)value : throw new InvalidDataException("文件偏移溢出");
    public ReadOnlySpan<byte> Span(long offset, int size) { Require(offset, checked((ulong)size)); return Bytes.AsSpan(checked((int)offset), size); }
    public byte Byte(long offset) => Span(offset, 1)[0];
    public ushort U16(long offset) => BinaryPrimitives.ReadUInt16LittleEndian(Span(offset, 2));
    public uint U32(long offset) => BinaryPrimitives.ReadUInt32LittleEndian(Span(offset, 4));
    public ulong U64(long offset) => BinaryPrimitives.ReadUInt64LittleEndian(Span(offset, 8));
    public long I64(long offset) => BinaryPrimitives.ReadInt64LittleEndian(Span(offset, 8));
    public string String(long offset, ulong size, uint index)
    {
        if (index >= size) throw new InvalidDataException("ELF section 名称越界");
        var data = Span(checked(offset + index), checked((int)(size - index)));
        var end = data.IndexOf((byte)0);
        if (end < 0) throw new InvalidDataException("ELF section 名称未终止");
        return Encoding.UTF8.GetString(data[..end]);
    }
}
