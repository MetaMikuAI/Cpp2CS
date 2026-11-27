using System.Buffers.Binary;
using System.Text;

namespace Cpp2CS.Input;

public sealed record ElfSegment(uint Type, uint Flags, ulong Offset, ulong Address, ulong FileSize, ulong MemorySize);
public sealed record ElfSection(string Name, uint Type, ulong Flags, ulong Address, ulong Offset, ulong Size, uint Link, ulong EntrySize);
public sealed record ElfSymbol(string Name, byte Info, byte Visibility, ushort Section, ulong Value, ulong Size);
public readonly record struct ElfRela(ulong Address, uint Type, uint Symbol, long Addend);

/// <summary>ELF gABI 的 Elf64_Ehdr、Phdr、Shdr、Sym、Rela。此层的地址均为链接虚拟地址。</summary>
public sealed class Elf64
{
    private readonly byte[] file;
    private readonly ElfSegment[] loads;
    private readonly Dictionary<ulong, int> relocationIndex = new();
    public ushort Machine { get; }
    public ulong ImageBase { get; }
    public IReadOnlyList<ElfSegment> Segments { get; }
    public IReadOnlyList<ElfSection> Sections { get; }
    public IReadOnlyList<ElfSymbol> DynamicSymbols { get; }
    public IReadOnlyList<ElfRela> Relocations { get; }
    public bool BindsLocally { get; }
    private readonly Lazy<Dictionary<int, string>> neededVersions;

    public string SourcePath { get; }
    public static Elf64 Load(string path) => new(File.ReadAllBytes(path), path);

    /// <summary>GNU 构建标识，同一映像的分离符号文件有相同标识。</summary>
    public string BuildId()
    {
        foreach (var section in Sections.Where(s => s.Type == 7))
        {
            var notes = Slice(section.Offset, section.Size);
            while (notes.Length >= 12)
            {
                int name = checked((int)U32(notes)), size = checked((int)U32(notes, 4));
                int data = checked(12 + ((name + 3) & ~3));
                int end = checked(data + ((size + 3) & ~3));
                if (end > notes.Length) throw new InvalidDataException("ELF 注记越界");
                if (U32(notes, 8) == 3 && size > 0 && notes.Slice(12, name).SequenceEqual("GNU\0"u8))
                    return Convert.ToHexString(notes.Slice(data, size));
                notes = notes[end..];
            }
        }
        throw new InvalidDataException("缺少 GNU 构建标识");
    }

    public IEnumerable<ElfSymbol> FunctionSymbols() => DefinedSymbols(2);
    public IEnumerable<ElfSymbol> ObjectSymbols() => DefinedSymbols(1);

    private IEnumerable<ElfSymbol> DefinedSymbols(int kind)
    {
        foreach (var section in Sections.Where(s => s.Type == 2))
        {
            if (section.EntrySize != 24 || section.Size % 24 != 0) throw new InvalidDataException("符号表步长无效");
            var strings = Sections[checked((int)section.Link)];
            for (ulong i = 0; i < section.Size; i += 24)
            {
                var s = Slice(section.Offset + i, 24);
                if ((s[4] & 15) == kind && U16(s, 6) != 0)
                    yield return new(CString(Slice(strings.Offset, strings.Size), U32(s)), s[4], s[5],
                        U16(s, 6), U64(s, 8), U64(s, 16));
            }
        }
    }

    private Elf64(byte[] file, string path)
    {
        this.file = file;
        SourcePath = path;
        var h = Slice(0, 64);
        if (!h[..7].SequenceEqual(new byte[] { 0x7f, 69, 76, 70, 2, 1, 1 }) || U16(h, 16) is not (2 or 3))
            throw new InvalidDataException("需要小端 ELF64 可执行文件或共享对象");
        Machine = U16(h, 18);
        if (Machine is not (62 or 183)) throw new NotSupportedException($"ELF 机器号 {Machine}");
        var ph = U64(h, 32);
        var sh = U64(h, 40);
        var phentsize = U16(h, 54);
        var shentsize = U16(h, 58);
        int shnum = U16(h, 60), names = U16(h, 62), phnum = U16(h, 56);
        if (sh != 0)
        {
            if (shentsize < 64) throw new InvalidDataException("ELF 节头过短");
            var zero = Slice(sh, 64);
            if (shnum == 0) shnum = checked((int)U64(zero, 32));
            if (names == 0xffff) names = checked((int)U32(zero, 40));
            if (phnum == 0xffff) phnum = checked((int)U32(zero, 44));
        }
        if (phentsize < 56 || phnum == 0) throw new InvalidDataException("ELF 程序头无效");
        var segments = new ElfSegment[phnum];
        for (int i = 0; i < segments.Length; i++)
        {
            var p = Slice(checked(ph + (ulong)i * phentsize), 56);
            var s = new ElfSegment(U32(p), U32(p, 4), U64(p, 8), U64(p, 16), U64(p, 32), U64(p, 40));
            Slice(s.Offset, s.FileSize);
            if (s.Type == 1 && (s.FileSize > s.MemorySize || s.MemorySize > ulong.MaxValue - s.Address))
                throw new InvalidDataException("PT_LOAD 的内存范围无效");
            segments[i] = s;
        }
        Segments = segments;
        loads = segments.Where(p => p.Type == 1).OrderBy(p => p.Address).ToArray();
        if (loads.Length == 0) throw new InvalidDataException("缺少 PT_LOAD");
        ImageBase = loads[0].Address;

        var sections = new ElfSection[shnum];
        var nameOffsets = new uint[shnum];
        if (shnum != 0) Slice(sh, checked((ulong)shnum * shentsize));
        for (int i = 0; i < sections.Length; i++)
        {
            var p = Slice(checked(sh + (ulong)i * shentsize), 64);
            nameOffsets[i] = U32(p);
            sections[i] = new("", U32(p, 4), U64(p, 8), U64(p, 16), U64(p, 24), U64(p, 32), U32(p, 40), U64(p, 56));
            if (sections[i].Type is not (0 or 8)) Slice(sections[i].Offset, sections[i].Size);
        }
        if (names != 0)
        {
            var strings = sections[names];
            var bytes = Slice(strings.Offset, strings.Size);
            for (int i = 0; i < sections.Length; i++) sections[i] = sections[i] with { Name = CString(bytes, nameOffsets[i]) };
        }
        Sections = sections;

        var tags = new Dictionary<ulong, ulong>();
        foreach (var p in segments.Where(p => p.Type == 2))
        {
            for (ulong i = 0; i + 16 <= p.FileSize; i += 16)
            {
                var item = Slice(p.Offset + i, 16);
                var tag = U64(item);
                if (tag == 0) break;
                tags[tag] = U64(item, 8);
            }
        }
        BindsLocally = U16(h, 16) == 2 || tags.ContainsKey(16) || (tags.GetValueOrDefault(30ul) & 2) != 0;
        DynamicSymbols = ReadSymbols(tags);
        neededVersions = new(ReadNeededVersions);
        var tables = new HashSet<(ulong Offset, ulong Size)>();
        foreach (var s in sections.Where(s => s.Type == 4 && (s.Flags & 2) != 0))
        {
            if (s.EntrySize != 24 || sections[s.Link].Type != 11) throw new InvalidDataException("动态 RELA 节的符号表或步长无效");
            tables.Add((s.Offset, s.Size));
        }
        void DynamicRela(ulong addressTag, ulong sizeTag)
        {
            if (tags.TryGetValue(addressTag, out var va) && tags[sizeTag] != 0)
                tables.Add(((ulong)RequireFileOffset(va, tags[sizeTag]), tags[sizeTag]));
        }
        if (tags.ContainsKey(7) && tags.GetValueOrDefault(9ul) != 24) throw new InvalidDataException("DT_RELAENT 无效");
        if (tags.ContainsKey(17) || tags.ContainsKey(36) || tags.ContainsKey(0x6000000f) || tags.ContainsKey(0x60000011))
            throw new NotSupportedException("输入含 REL、RELR 或 Android 压缩重定位");
        DynamicRela(7, 8);
        if (tags.ContainsKey(23))
        {
            if (tags[20] != 7) throw new NotSupportedException("PLT 重定位需要 RELA");
            DynamicRela(23, 2);
        }
        var records = new List<ElfRela>(checked((int)tables.Sum(t => (long)t.Size / 24)));
        foreach (var (offset, size) in tables.OrderBy(t => t.Offset))
        {
            if (size % 24 != 0) throw new InvalidDataException("RELA 表尾不完整");
            var table = Slice(offset, size);
            for (int i = 0; i < table.Length; i += 24)
            {
                var r = new ElfRela(U64(table, i), U32(table, i + 8), U32(table, i + 12), unchecked((long)U64(table, i + 16)));
                if (r.Type != 0 && !relocationIndex.TryAdd(r.Address, records.Count))
                    throw new InvalidDataException($"重定位地址重复 0x{r.Address:x}");
                records.Add(r);
            }
        }
        Relocations = records;
    }

    private ElfSymbol[] ReadSymbols(Dictionary<ulong, ulong> tags)
    {
        ulong offset, count, str, length;
        if (Sections.SingleOrDefault(s => s.Type == 11) is { } symbols)
        {
            if (symbols.EntrySize != 24 || symbols.Size % 24 != 0) throw new InvalidDataException("动态符号表步长无效");
            offset = symbols.Offset;
            count = symbols.Size / 24;
            var names = Sections[(int)symbols.Link];
            str = names.Offset;
            length = names.Size;
        }
        else if (tags.TryGetValue(6, out var va))
        {
            if (tags[11] != 24) throw new InvalidDataException("DT_SYMENT 无效");
            count = tags.TryGetValue(4, out var hash) ? Word(hash + 4) : GnuSymbolCount(tags[0x6ffffef5]);
            offset = (ulong)RequireFileOffset(va, checked(count * 24));
            length = tags[10];
            str = (ulong)RequireFileOffset(tags[5], length);
        }
        else return [];
        var rows = Slice(offset, checked(count * 24));
        var strings = Slice(str, length);
        var result = new ElfSymbol[checked((int)count)];
        for (int i = 0; i < result.Length; i++)
        {
            var s = rows[(i * 24)..];
            result[i] = new(CString(strings, U32(s)), s[4], s[5], U16(s, 6), U64(s, 8), U64(s, 16));
        }
        return result;
    }

    private uint GnuSymbolCount(ulong hash)
    {
        uint nbuckets = Word(hash), first = Word(hash + 4);
        var buckets = checked(hash + 16 + 8ul * Word(hash + 8));
        var chains = checked(buckets + 4ul * nbuckets);
        uint last = 0;
        for (uint i = 0; i < nbuckets; i++) last = Math.Max(last, Word(buckets + 4ul * i));
        if (last == 0) return first;
        if (last < first) throw new InvalidDataException("GNU 哈希桶起点越界");
        while ((Word(checked(chains + 4ul * (last - first))) & 1) == 0) last = checked(last + 1);
        return checked(last + 1);
    }

    internal ReadOnlySpan<byte> Slice(ulong offset, ulong size)
    {
        if (offset > (ulong)file.Length || size > (ulong)file.Length - offset)
            throw new InvalidDataException($"ELF 文件范围越界 0x{offset:x}+0x{size:x}");
        return file.AsSpan((int)offset, (int)size);
    }

    internal static ushort U16(ReadOnlySpan<byte> bytes, int at = 0) => BinaryPrimitives.ReadUInt16LittleEndian(bytes[at..]);
    internal static uint U32(ReadOnlySpan<byte> bytes, int at = 0) => BinaryPrimitives.ReadUInt32LittleEndian(bytes[at..]);
    internal static ulong U64(ReadOnlySpan<byte> bytes, int at = 0) => BinaryPrimitives.ReadUInt64LittleEndian(bytes[at..]);
    internal static string CString(ReadOnlySpan<byte> bytes, uint index)
    {
        var tail = bytes[checked((int)index)..];
        int end = tail.IndexOf((byte)0);
        if (end < 0) throw new InvalidDataException("字符串超出表尾");
        return Encoding.UTF8.GetString(tail[..end]);
    }

    private ElfSegment? LoadAt(ulong va, ulong size)
    {
        foreach (var s in loads)
            if (va >= s.Address && va - s.Address < s.MemorySize && size <= s.MemorySize - (va - s.Address)) return s;
        return null;
    }

    public int? FileOffset(ulong va, ulong size = 1)
    {
        var s = LoadAt(va, size);
        if (s == null) return null;
        ulong delta = va - s.Address;
        return delta <= s.FileSize && size <= s.FileSize - delta ? checked((int)(s.Offset + delta)) : null;
    }

    internal int RequireFileOffset(ulong va, ulong size) =>
        FileOffset(va, size) ?? throw new InvalidDataException($"虚拟地址没有文件内容 0x{va:x}+0x{size:x}");
    internal bool IsExecutable(ulong va) => LoadAt(va, 1) is { Flags: var flags } && (flags & 1) != 0;
    internal bool Mapped(ulong va, ulong size) => LoadAt(va, size) != null;
    internal uint Word(ulong va) => (uint)Number(va, 4);
    internal byte Byte(ulong va) => (byte)Number(va, 1);

    private ulong Number(ulong va, int width)
    {
        var s = LoadAt(va, (ulong)width) ?? throw new InvalidDataException($"地址未映射 0x{va:x}");
        var delta = va - s.Address;
        if (delta >= s.FileSize) return 0;
        int n = (int)Math.Min((ulong)width, s.FileSize - delta);
        var bytes = file.AsSpan(checked((int)(s.Offset + delta)), n);
        if (n == 8) return U64(bytes);
        if (n == 4) return U32(bytes);
        ulong result = 0;
        for (int i = 0; i < n; i++) result |= (ulong)bytes[i] << (8 * i);
        return result;
    }

    internal bool TryPointer(ulong slot, out ulong value)
    {
        value = 0;
        if (!Mapped(slot, 8)) return false;
        if (!relocationIndex.TryGetValue(slot, out int index))
        {
            value = Number(slot, 8);
            return true;
        }
        var r = Relocations[index];
        if (r.Type == (Machine == 183 ? 1027u : 8u) && r.Symbol == 0)
        {
            value = unchecked((ulong)r.Addend);
            return true;
        }
        bool absolute = Machine == 183 ? r.Type is 257 or 1025 or 1026 : r.Type is 1 or 6 or 7;
        if (!absolute || r.Symbol >= DynamicSymbols.Count) return false;
        var symbol = DynamicSymbols[(int)r.Symbol];
        if (symbol.Section == 0 || (symbol.Info & 15) == 10) return false;
        value = Machine == 62 && r.Type is 6 or 7 ? symbol.Value : unchecked(symbol.Value + (ulong)r.Addend);
        return true;
    }

    public ulong Pointer(ulong slot) => TryPointer(slot, out var value) ? value :
        throw new InvalidDataException($"指针无法在映像中解析 0x{slot:x}");

    private Dictionary<int, string> ReadNeededVersions()
    {
        var result = new Dictionary<int, string>();
        foreach (var verneed in Sections.Where(s => s.Type == 0x6ffffffe))
        {
            var namesSection = Sections[(int)verneed.Link];
            var strings = Slice(namesSection.Offset, namesSection.Size);
            var needs = Slice(verneed.Offset, verneed.Size);
            while (needs.Length >= 16)
            {
                if (U16(needs) != 1) throw new InvalidDataException("ELF 符号版本记录无效");
                string library = CString(strings, U32(needs, 4));
                int aux = checked((int)U32(needs, 8));
                for (int j = 0; j < U16(needs, 2); j++)
                {
                    if (aux > needs.Length - 16) throw new InvalidDataException("ELF 符号版本索引越界");
                    var a = needs[aux..];
                    string version = CString(strings, U32(a, 8));
                    result.Add(U16(a, 6) & 0x7fff, $"{library.Length}:{library}{version}");
                    aux = checked(aux + (int)U32(a, 12));
                }
                int next = checked((int)U32(needs, 12));
                if (next == 0) break;
                if (next < 16 || next > needs.Length - 16) throw new InvalidDataException("ELF 符号版本链越界");
                needs = needs[next..];
            }
        }
        return result;
    }

    /// <summary>动态查找包括名字、绑定与 GNU 版本；版本号只在本映像内有意义。</summary>
    public string? SymbolIdentity(uint index)
    {
        var symbol = DynamicSymbols[(int)index];
        if (symbol.Name.Length == 0) return null;
        string? requirement = "";
        if (Sections.SingleOrDefault(s => s.Type == 0x6fffffff) is { } versions)
        {
            if (2ul * index + 2 > versions.Size) return null;
            int version = U16(Slice(versions.Offset + 2ul * index, 2)) & 0x7fff;
            if (version > 1)
            {
                if (symbol.Section == 0)
                {
                    if (!neededVersions.Value.TryGetValue(version, out requirement)) return null;
                }
                else if ((requirement = DefinedVersion(version)) == null) return null;
            }
        }
        return $"{symbol.Info}:{symbol.Name.Length}:{symbol.Name}{requirement}";
    }

    private string? DefinedVersion(int version)
    {
        var section = Sections.SingleOrDefault(s => s.Type == 0x6ffffffd);
        if (section == null) return null;
        var names = Sections[(int)section.Link];
        var records = Slice(section.Offset, section.Size);
        while (records.Length >= 20)
        {
            if (U16(records) != 1) throw new InvalidDataException("ELF 符号版本定义无效");
            if ((U16(records, 4) & 0x7fff) == version && U16(records, 6) != 0)
            {
                int aux = checked((int)U32(records, 12));
                if (aux > records.Length - 8) throw new InvalidDataException("ELF 符号版本名越界");
                return CString(Slice(names.Offset, names.Size), U32(records, aux));
            }
            int next = checked((int)U32(records, 16));
            if (next == 0) break;
            if (next < 20 || next > records.Length - 20) throw new InvalidDataException("ELF 符号版本定义链越界");
            records = records[next..];
        }
        return null;
    }
    internal bool MatchString(ulong va, byte[] terminated)
    {
        var at = FileOffset(va, (ulong)terminated.Length);
        return at.HasValue && file.AsSpan(at.Value, terminated.Length).SequenceEqual(terminated);
    }
}
