using System.Buffers.Binary;
using System.Text;

namespace Cpp2CS.Targets.Elf;

internal sealed record ImageRange(string Name, ulong Address, long FileOffset, ulong FileSize, ulong MemorySize, bool Executable, bool Writable);
internal enum AddressKind { FileBacked, ZeroFill, Unmapped }
internal sealed record AddressResolution(AddressKind Kind, ImageRange? Range, long? FileOffset, ulong AvailableBytes);
internal sealed record CodeRelocation(ulong Address, int Size, string Kind, long RecordFileOffset);
/// <summary>节头表中的一节。Flags 为 ELF sh_flags（2 SHF_ALLOC，4 SHF_EXECINSTR）。</summary>
internal sealed record ImageSection(string Name, ulong Address, ulong Size, uint Type, ulong Flags)
{
    internal bool Executable => (Flags & 4) != 0;
    internal bool Contains(ulong address) => address >= Address && address - Address < Size;
}
internal sealed record RelocationTableSummary(string Name, string Format, long FileOffset, ulong Size, long Records, long Fixups, IReadOnlyDictionary<string, long> Kinds);

internal sealed class ImageDocument
{
    private readonly byte[] bytes;
    internal ReadOnlyMemory<byte> Bytes => bytes;

    internal List<(string Name, ulong Value, ulong Size)> FunctionSymbols { get; private init; } = [];
    internal Dictionary<ulong, long> ImportAddends { get; private init; } = [];
    internal List<RawRelocation> Relocations { get; private init; } = [];
    internal ulong PreferredBase { get; }
    internal bool PositionIndependent { get; private init; }
    internal ushort Machine { get; private init; }
    internal IReadOnlyList<ImageRange> Ranges { get; }
    internal IReadOnlyList<ImageRange> ExecutableRanges { get; }
    internal IReadOnlyList<RelocationTableSummary> RelocationTables { get; }
    internal IReadOnlyList<CodeRelocation> CodeRelocations { get; }
    private readonly int maximumRelocationSize;

    /// <summary>ELF PT_GNU_EH_FRAME 指向的 .eh_frame_hdr 虚拟地址。</summary>
    internal ulong? EhFrameHeader { get; private init; }

    private IReadOnlyDictionary<ulong, ulong> pointerFixups = new Dictionary<ulong, ulong>();

    /// <summary>加载器重定位记录明确指定的指针；不把文件中的任意整数当作地址。</summary>
    internal ulong? RelocatedPointer(ulong address) => pointerFixups.TryGetValue(address, out var target) ? target : null;

    /// <summary>重定位记录给出的全部指针值（可能重复）。</summary>
    internal IEnumerable<ulong> RelocatedPointerTargets() => pointerFixups.Values;

    /// <summary>重定位指针：(指针所在地址, 指针值)。</summary>
    internal IEnumerable<KeyValuePair<ulong, ulong>> RelocatedPointers => pointerFixups;

    /// <summary>引用未定义动态符号的指针位置（GOT、JUMP_SLOT）及符号名。</summary>
    internal IReadOnlyDictionary<ulong, string> Imports { get; private init; } = new Dictionary<ulong, string>();

    /// <summary>ELF DT_NEEDED 中声明的动态库名，不从导入符号名推测库名。</summary>
    internal IReadOnlyList<string> NeededLibraries { get; private init; } = [];

    /// <summary>按符号重定位的指针位置及符号名，含已定义符号（如静态链接并导出的 libc++abi 经 PLT 引用）。</summary>
    internal IReadOnlyDictionary<ulong, string> SymbolSlots { get; private init; } = new Dictionary<ulong, string>();

    /// <summary>有地址的节（ELF SHF_ALLOC 节），按地址升序。</summary>
    internal IReadOnlyList<ImageSection> Sections { get; private init; } = [];

    internal ImageSection? Section(string name) => Sections.FirstOrDefault(s => s.Name == name);

    internal ImageSection? SectionAt(ulong address) => Sections.FirstOrDefault(s => s.Contains(address));

    /// <summary>ELF 加载器完成重定位后保护为只读的范围。</summary>
    internal IReadOnlyList<(ulong Address, ulong Size)> RelroRanges { get; private init; } = [];

    /// <summary>导出符号：ELF 动态符号表中已定义的非局部符号。</summary>
    internal IReadOnlyDictionary<string, ulong> Exports { get; private init; } = new Dictionary<string, ulong>();

    private ImageDocument(byte[] bytes, ulong preferredBase, List<ImageRange> ranges,
        List<RelocationTableSummary> tables, List<CodeRelocation> codeRelocations)
    {
        this.bytes = bytes;
        PreferredBase = preferredBase;
        Ranges = ranges.OrderBy(r => r.Address).ToArray();
        ExecutableRanges = Ranges.Where(r => r.Executable).ToArray();
        RelocationTables = tables.ToArray();
        CodeRelocations = codeRelocations.OrderBy(r => r.Address).ToArray();
        maximumRelocationSize = codeRelocations.Count == 0 ? 0 : CodeRelocations.Max(r => r.Size);
    }

    internal static ImageDocument Load(string path) => Parse(File.ReadAllBytes(path));

    internal static ImageDocument Parse(byte[] bytes)
    {
        var reader = new ImageReader(bytes);
        if (reader.U32(0) == 0x464c457f) return LoadElf(reader);
        throw new InvalidDataException("需要 ELF64 AArch64 或 x86_64 文件");
    }

    internal AddressResolution Resolve(ulong address)
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

    internal bool IsExecutable(ulong address)
    {
        var mapping = Resolve(address);
        return mapping.Kind == AddressKind.FileBacked && mapping.Range!.Executable;
    }

    /// <summary>读取文件中实际存在的字节；未映射或越过文件内容时抛出。</summary>
    internal ReadOnlySpan<byte> Read(ulong address, int size)
    {
        var mapping = Resolve(address);
        if (mapping.Kind != AddressKind.FileBacked || (ulong)size > mapping.AvailableBytes)
            throw new InvalidDataException($"地址未完整映射到文件：0x{address:X}+{size}");
        return bytes.AsSpan(checked((int)mapping.FileOffset!.Value), size);
    }

    /// <summary>读取至多 size 个文件字节；遇到映射末尾时截短，未映射时为空。</summary>
    internal ReadOnlySpan<byte> ReadUpTo(ulong address, int size)
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
    internal ulong? ReadPointer(ulong address)
    {
        if (pointerFixups.TryGetValue(address, out var value)) return value;
        if (Imports.ContainsKey(address)) return null;
        var mapping = Resolve(address);
        if (mapping.Kind == AddressKind.ZeroFill) return 0;
        return ReadU64(address);
    }

    internal uint ReadU32(ulong address) => BinaryPrimitives.ReadUInt32LittleEndian(Read(address, 4));
    internal ulong ReadU64(ulong address) => BinaryPrimitives.ReadUInt64LittleEndian(Read(address, 8));
    internal int ReadI32(ulong address) => BinaryPrimitives.ReadInt32LittleEndian(Read(address, 4));

    internal bool HasCodeRelocation(ulong address, int size)
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
        if (reader.Byte(4) != ElfConstants.Class64) throw new NotSupportedException($"ELF class {reader.Byte(4)} 未支持，需要 ELF64");
        if (reader.Byte(5) != ElfConstants.LittleEndian) throw new NotSupportedException($"ELF byte order {reader.Byte(5)} 未支持，需要小端");
        if (reader.U16(18) is not (ElfConstants.AArch64 or ElfConstants.X86_64)) throw new NotSupportedException($"ELF machine {reader.U16(18)} 未支持");
        if (reader.Byte(6) != 1 || reader.U32(20) != 1 || reader.U16(16) is not (ElfConstants.EtExec or ElfConstants.EtDyn) || reader.U16(52) != 64)
            throw new InvalidDataException("需要有效 ELF64 ET_EXEC/ET_DYN 头");
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
                ranges.Add(new($"LOAD[{i}]", address, offset, fileSize, memorySize, (reader.U32(p + 4) & 1) != 0, (reader.U32(p + 4) & 2) != 0));
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
        var collector = new RelocationCollector(reader, ranges, reader.U16(18));
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
        var functionSymbols = new List<(string Name, ulong Value, ulong Size)>();
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
            if (type is 2 or 11)
            {
                var link = reader.U32(s + 40);
                if (link >= shcount || reader.U64(s + 56) != 24 || reader.U64(s + 32) % 24 != 0) throw new InvalidDataException("符号表长度或链接错误");
                var str = shoff + link * 64L;
                var off = reader.Offset(reader.U64(s + 24));
                var size = reader.U64(s + 32);
                reader.Require(off, size);
                for (ulong n = 24; n < size; n += 24)
                {
                    var at = off + (long)n;
                    if ((reader.Byte(at + 4) & 15) == 2 && reader.U16(at + 6) is > 0 and < 0xff00 && reader.U64(at + 16) != 0)
                        functionSymbols.Add((reader.String(reader.Offset(reader.U64(str + 24)), reader.U64(str + 32), reader.U32(at)), reader.U64(at + 8), reader.U64(at + 16)));
                }
            }
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
                if (tag is 2 or 5 or 6 or 7 or 8 or 9 or 10 or 17 or 18 or 19 or 20 or 23 or 35 or 36 or 37 or 0x6000000f or 0x60000011 or 0x6fffe000 or 0x6fffe001 or 0x6fffe003)
                {
                    var value = reader.U64(p + 8);
                    if (!tags.TryAdd(tag, value) && tags[tag] != value) throw new InvalidDataException("重复 ELF dynamic relocation tag 不一致");
                }
            }
            if (!terminated) throw new InvalidDataException("ELF dynamic table 缺少 DT_NULL");
            if (tags.ContainsKey(6) && symbols.Count == 0)
                throw new NotSupportedException("没有节头的动态符号表尚未支持，不能确认导入导出完整性");
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
        var importAddends = new Dictionary<ulong, long>();
        var imports = new Dictionary<ulong, string>();
        var slots = new Dictionary<ulong, string>();
        foreach (var (address, (symbol, addend)) in collector.SymbolPointers)
        {
            if (symbol >= symbols.Count) throw new InvalidDataException($"重定位符号索引越界：{symbol}");
            var entry = symbols[(int)symbol];
            if (entry.Name.Length > 0) slots[address] = entry.Name;
            if (entry.Defined) fixups[address] = unchecked(entry.Value + (ulong)addend);
            else { imports[address] = entry.Name; importAddends[address] = addend; }
        }
        return new(reader.Bytes, ranges.Min(r => r.Address), ranges, collector.Summaries, collector.CodeRelocations)
        {
            PositionIndependent = reader.U16(16) == ElfConstants.EtDyn,
            Machine = reader.U16(18),
            FunctionSymbols = functionSymbols,
            Relocations = collector.Relocations,
            EhFrameHeader = ehFrameHeader,
            RelroRanges = relroRanges,
            Sections = sections.OrderBy(x => x.Address).ToArray(),
            Exports = exports,
            Imports = imports,
            ImportAddends = importAddends,
            NeededLibraries = neededLibraries.Distinct(StringComparer.Ordinal).ToArray(),
            SymbolSlots = slots,
            pointerFixups = fixups,
        };
    }

    // SHT_DYNSYM：symbols 按索引保存全部条目供重定位解析；exports 收集已定义的非局部符号。
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
            if ((info >> 4) == 0 || index == 0 || index >= 0xff00 || (reader.Byte(p + 5) & 3) is 1 or 2) continue;
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

}

internal sealed class ImageReader(byte[] bytes)
{
    internal byte[] Bytes { get; } = bytes;
    internal void Require(long offset, ulong size)
    {
        if (offset < 0 || (ulong)offset > (ulong)Bytes.LongLength || size > (ulong)Bytes.LongLength - (ulong)offset)
            throw new InvalidDataException($"文件范围越界：0x{offset:X}+0x{size:X}");
    }
    internal long Offset(ulong value) => value <= long.MaxValue ? (long)value : throw new InvalidDataException("文件偏移溢出");
    internal ReadOnlySpan<byte> Span(long offset, int size) { Require(offset, checked((ulong)size)); return Bytes.AsSpan(checked((int)offset), size); }
    internal byte Byte(long offset) => Span(offset, 1)[0];
    internal ushort U16(long offset) => BinaryPrimitives.ReadUInt16LittleEndian(Span(offset, 2));
    internal uint U32(long offset) => BinaryPrimitives.ReadUInt32LittleEndian(Span(offset, 4));
    internal ulong U64(long offset) => BinaryPrimitives.ReadUInt64LittleEndian(Span(offset, 8));
    internal long I64(long offset) => BinaryPrimitives.ReadInt64LittleEndian(Span(offset, 8));
    internal string String(long offset, ulong size, uint index)
    {
        if (index >= size) throw new InvalidDataException("ELF section 名称越界");
        var data = Span(checked(offset + index), checked((int)(size - index)));
        var end = data.IndexOf((byte)0);
        if (end < 0) throw new InvalidDataException("ELF section 名称未终止");
        return Encoding.UTF8.GetString(data[..end]);
    }
}
