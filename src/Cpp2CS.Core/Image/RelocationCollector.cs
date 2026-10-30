
namespace Cpp2CS.Image;

internal sealed class RelocationCollector(ImageReader reader, List<ImageRange> ranges)
{
    private sealed record Table(string Name, string Format, long Offset, ulong Size, ulong Stride);
    private readonly List<Table> tables = [];
    private readonly ImageRange[] executable = ranges.Where(r => r.Executable).ToArray();
    public List<RelocationTableSummary> Summaries { get; } = [];
    public List<CodeRelocation> CodeRelocations { get; } = [];
    /// <summary>RELATIVE 重定位：目标地址处指针的加载后值（基址 0）。</summary>
    public Dictionary<ulong, ulong> Pointers { get; } = new();
    /// <summary>ABS64/GLOB_DAT/JUMP_SLOT：目标地址处指针引用的动态符号与加数，待符号表解析。</summary>
    public Dictionary<ulong, (uint Symbol, long Addend)> SymbolPointers { get; } = new();

    public void Add(string name, string format, long offset, ulong size, ulong stride)
    {
        reader.Require(offset, size);
        if (size % stride != 0) throw new InvalidDataException($"{name} relocation table 长度错误");
        if (size == 0) return;
        foreach (var table in tables)
        {
            if (table.Offset == offset && table.Size == size && table.Format == format) return;
            if ((ulong)offset < (ulong)table.Offset + table.Size && (ulong)table.Offset < (ulong)offset + size)
                throw new NotSupportedException("重定位表部分重叠，不能重复统计或忽略");
        }
        tables.Add(new(name, format, offset, size, stride));
    }

    public void ScanElf()
    {
        foreach (var table in tables)
        {
            var kinds = new Dictionary<string, long>();
            long fixups = 0;
            ulong next = 0;
            var haveBase = false;
            for (ulong i = 0; i < table.Size; i += table.Stride)
            {
                var position = checked(table.Offset + (long)i);
                var address = reader.U64(position);
                if (table.Format == "RELR")
                {
                    if ((address & 1) == 0)
                    {
                        if (address % 8 != 0) throw new InvalidDataException("RELR 地址未按指针宽度对齐");
                        Record(address, 8, "AARCH64_RELR", position, kinds);
                        fixups++;
                        next = checked(address + 8);
                        haveBase = true;
                    }
                    else
                    {
                        if (!haveBase) throw new InvalidDataException("RELR bitmap 缺少基地址");
                        for (var bit = 1; bit < 64; bit++)
                            if ((address & (1UL << bit)) != 0)
                            {
                                Record(checked(next + (ulong)(bit - 1) * 8), 8, "AARCH64_RELR", position, kinds);
                                fixups++;
                            }
                        next = checked(next + 63 * 8);
                    }
                    continue;
                }
                var info = reader.U64(position + 8);
                var kind = (uint)info;
                var size = ElfWidth(kind);
                if (size == 0) { Increment(kinds, "AARCH64_NONE"); continue; }
                Record(address, size, $"AARCH64_{kind}", position, kinds);
                // REL 格式的加数在目标位置本身，读取时取文件内容即可，不进入表
                if (table.Format == "RELA")
                {
                    var addend = reader.I64(position + 16);
                    if (kind == 1027) Pointers[address] = (ulong)addend;
                    else if (kind is 257 or 1025 or 1026) SymbolPointers[address] = ((uint)(info >> 32), addend);
                }
                fixups++;
            }
            Summaries.Add(new(table.Name, table.Format, table.Offset, table.Size, checked((long)(table.Size / table.Stride)), fixups, kinds));
        }
    }

    public void ScanPe(long offset, uint size, ulong imageBase)
    {
        reader.Require(offset, size);
        var kinds = new Dictionary<string, long>();
        long records = 0;
        long fixups = 0;
        ulong consumed = 0;
        while (consumed < size)
        {
            if (size - consumed < 8) throw new InvalidDataException("PE relocation block 头截断");
            var block = checked(offset + (long)consumed);
            var page = reader.U32(block);
            var blockSize = reader.U32(block + 4);
            if (page % 4096 != 0 || blockSize < 8 || blockSize % 2 != 0 || blockSize > size - consumed)
                throw new InvalidDataException("PE relocation block 长度或页地址错误");
            for (uint i = 8; i < blockSize; i += 2)
            {
                var position = checked(block + i);
                var item = reader.U16(position);
                var kind = item >> 12;
                records++;
                if (kind == 0) { Increment(kinds, "PE_ABSOLUTE_PADDING"); continue; }
                var width = kind switch
                {
                    1 or 2 => 2,
                    3 => 4,
                    4 => 2,
                    10 => 8,
                    _ => throw new NotSupportedException($"AMD64 relocation type {kind} 未支持，不能确认代码覆盖")
                };
                if (kind == 4)
                {
                    if (i + 2 >= blockSize) throw new InvalidDataException("PE HIGHADJ 缺少调整值");
                    i += 2;
                    records++;
                }
                var address = checked(imageBase + page + (uint)(item & 0xfff));
                Record(address, width, $"PE_{kind}", position, kinds);
                fixups++;
            }
            consumed += blockSize;
        }
        Summaries.Add(new("BaseRelocationDirectory", "PE_BASE", offset, size, records, fixups, kinds));
    }

    private void Record(ulong address, int size, string kind, long position, Dictionary<string, long> kinds)
    {
        var end = checked(address + (ulong)size);
        if (!ranges.Any(r => address >= r.Address && address - r.Address < r.MemorySize && (ulong)size <= r.MemorySize - (address - r.Address)))
            throw new InvalidDataException($"重定位目标不在完整映像范围内：0x{address:X}+{size}");
        Increment(kinds, kind);
        if (executable.Any(r => address < checked(r.Address + r.MemorySize) && end > r.Address))
            CodeRelocations.Add(new(address, size, kind, position));
    }

    private static int ElfWidth(uint kind) => kind switch
    {
        0 => 0,
        257 or 260 or 307 or 1025 or 1026 or 1027 or 1028 or 1029 or 1030 or 1032 => 8,
        258 or 261 or 308 => 4,
        259 or 262 => 2,
        >= 263 and <= 280 or >= 282 and <= 293 or >= 300 and <= 306 or >= 309 and <= 312 => 4,
        >= 512 and <= 559 => 4,
        1031 => 16,
        _ => throw new NotSupportedException($"AArch64 relocation type {kind} 未支持，不能确认代码覆盖")
    };

    private static void Increment(Dictionary<string, long> counts, string kind) => counts[kind] = counts.GetValueOrDefault(kind) + 1;
}
