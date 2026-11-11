using System.Collections.Immutable;
using Cpp2CS.Native.Images;
using NeutralRange = Cpp2CS.Native.Images.ImageRange;

namespace Cpp2CS.Targets.Elf;

/// <summary>装配处创建实现；消费者仅依赖 IImage。</summary>
public static class ElfImage
{
    public static IImage Load(string path) => new LoadedImage(File.ReadAllBytes(path));
    public static IImage Parse(ReadOnlySpan<byte> bytes) => new LoadedImage(bytes.ToArray());
}

internal sealed class LoadedImage : IImage
{
    private readonly ImageDocument document;
    private readonly ulong[] relocationEnds;
    public ulong PreferredBase => document.PreferredBase;
    public int PointerWidth => 8;
    public ByteOrder ByteOrder => ByteOrder.LittleEndian;
    public ImmutableArray<NeutralRange> Ranges { get; }
    public IReadOnlyList<ImageRelocation> Relocations { get; }
    public ImmutableArray<ImportSymbol> Imports { get; }
    public ImmutableArray<ExportSymbol> Exports { get; }
    public ImmutableArray<FunctionSymbol> FunctionSymbols { get; }
    public ImmutableArray<FunctionRange> Functions { get; }
    public ImmutableArray<TryRegion> TryRegions { get; }
    public ImmutableArray<string> Diagnostics { get; }

    internal LoadedImage(byte[] bytes)
    {
        document = ImageDocument.Parse(bytes);
        var ranges = new List<NeutralRange>();
        foreach (var r in document.Ranges)
        {
            if (r.FileSize != 0) ranges.Add(new(Offset(r.Address), r.FileSize, StorageKind.FileContent, r.Executable, r.Writable));
            if (r.MemorySize > r.FileSize) ranges.Add(new(Offset(r.Address + r.FileSize), r.MemorySize - r.FileSize, StorageKind.ZeroFill, r.Executable, r.Writable));
        }
        // 重定位完成后的保护范围可用于上层只读数据折叠。
        foreach (var protection in document.RelroRanges)
        {
            var first = Offset(protection.Address);
            var end = checked(first + protection.Size);
            var split = new List<NeutralRange>();
            foreach (var r in ranges)
            {
                var limit = checked(r.Start + r.Length);
                if (r.Start >= end || limit <= first) { split.Add(r); continue; }
                if (r.Start < first) split.Add(r with { Length = first - r.Start });
                var overlap = Math.Max(first, r.Start);
                var overlapEnd = Math.Min(end, limit);
                split.Add(r with { Start = overlap, Length = overlapEnd - overlap, Writable = false });
                if (limit > end) split.Add(r with { Start = end, Length = limit - end });
            }
            ranges = split;
        }
        Ranges = ranges.ToImmutableArray();
        document.Relocations.Sort((a, b) => a.Address.CompareTo(b.Address));
        Relocations = new RelocationView(this);
        relocationEnds = new ulong[Relocations.Count];
        for (var i = 0; i < document.Relocations.Count; i++)
        {
            var r = document.Relocations[i];
            if (i > 0 && document.Relocations[i - 1].Address == r.Address)
                throw new InvalidDataException("同一位置存在多个重定位");
            relocationEnds[i] = Math.Max(i == 0 ? 0 : relocationEnds[i - 1], checked(Offset(r.Address) + (ulong)r.Width));
        }
        Imports = document.Imports.Values.Distinct().Order().Select(n => new ImportSymbol(n)).ToImmutableArray();
        Exports = document.Exports.Select(e => new ExportSymbol(e.Key, InternalTarget(e.Value))).ToImmutableArray();
        FunctionSymbols = document.FunctionSymbols.Select(s => new FunctionSymbol(s.Name, Offset(s.Value), s.Size)).ToImmutableArray();
        var unwind = new UnwindReader(this, document);
        var functions = unwind.Functions.ToList();
        foreach (var symbol in document.FunctionSymbols)
        {
            var offset = Offset(symbol.Value);
            if (!IsExecutable(offset, Math.Max(1, symbol.Size))) throw new InvalidDataException("函数符号范围不在可执行映射内");
            if (symbol.Size != 0) functions.Add(new(offset, symbol.Size, FunctionEvidence.SymbolTable));
        }
        var diagnostics = unwind.Diagnostics.ToList();
        Functions = functions.GroupBy(f => f.Start).OrderBy(g => g.Key).Select(g =>
        {
            var extents = g.GroupBy(f => f.Length).OrderBy(e => e.Key)
                .Select(e => new FunctionExtent(e.Key, e.Aggregate((FunctionEvidence)0, (flags, f) => flags | f.Evidence))).ToImmutableArray();
            if (extents.Length > 1) diagnostics.Add($"函数 0x{g.Key:x} 范围证据冲突：" + string.Join(", ", extents.Select(e => $"{e.Evidence}={e.Length}")));
            return new FunctionRange(g.Key, extents.Max(e => e.Length), extents.Aggregate((FunctionEvidence)0, (flags, e) => flags | e.Evidence)) { Extents = extents };
        }).ToImmutableArray();
        TryRegions = unwind.Regions.ToImmutableArray();
        Diagnostics = diagnostics.ToImmutableArray();
    }

    internal ulong Offset(ulong address) => address >= PreferredBase ? address - PreferredBase : throw new InvalidDataException("地址低于映像基址");
    internal PointerTarget InternalTarget(ulong address) => new PointerTarget.Internal(unchecked(address - PreferredBase));

    // 紧凑记录保留在文档中；对外按索引或枚举按需生成目标。
    private sealed class RelocationView(LoadedImage image) : IReadOnlyList<ImageRelocation>
    {
        public int Count => image.document.Relocations.Count;
        public ImageRelocation this[int index]
        {
            get
            {
                var r = image.document.Relocations[index];
                var kind = ElfConstants.Classify(image.document.Machine, r.Kind);
                PointerTarget target = new PointerTarget.Unknown("该重定位不能静态化为映像指针");
                if (kind == RelocationKind.Pointer)
                {
                    if (image.document.Imports.TryGetValue(r.Address, out var name))
                        target = new PointerTarget.Import(new(name), image.document.ImportAddends.GetValueOrDefault(r.Address));
                    else if (image.document.RelocatedPointer(r.Address) is { } value) target = image.InternalTarget(value);
                    else target = new PointerTarget.Unknown("重定位缺少目标");
                }
                return new(image.Offset(r.Address), r.Width, kind, target);
            }
        }
        public IEnumerator<ImageRelocation> GetEnumerator() { for (var i = 0; i < Count; i++) yield return this[i]; }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    public AddressInfo Query(ulong offset)
    {
        int low = 0, high = Ranges.Length - 1;
        while (low <= high)
        {
            var mid = low + (high - low) / 2;
            var r = Ranges[mid];
            if (offset < r.Start) high = mid - 1;
            else if (offset - r.Start >= r.Length) low = mid + 1;
            else return new(r.Storage, r.Length - (offset - r.Start), r.Executable, r.Writable);
        }
        return new(StorageKind.Unmapped, 0, false, false);
    }

    private bool HasPermission(ulong offset, ulong length, bool executable)
    {
        if (length == 0 || length > ulong.MaxValue - offset) return false;
        while (length != 0)
        {
            var q = Query(offset);
            if (q.Storage == StorageKind.Unmapped || !(executable ? q.Executable : q.Writable)) return false;
            var n = Math.Min(length, q.AvailableBytes);
            offset += n;
            length -= n;
        }
        return true;
    }
    public bool IsExecutable(ulong offset, ulong length = 1) => HasPermission(offset, length, true);
    public bool IsWritable(ulong offset, ulong length = 1) => HasPermission(offset, length, false);
    public void ReadBytes(ulong offset, Span<byte> destination)
    {
        if ((ulong)destination.Length > ulong.MaxValue - offset) throw new InvalidDataException("读取地址溢出");
        while (!destination.IsEmpty)
        {
            var q = Query(offset);
            if (q.Storage == StorageKind.Unmapped) throw new InvalidDataException($"未映射地址 0x{offset:x}");
            var n = (int)Math.Min((ulong)destination.Length, q.AvailableBytes);
            if (q.Storage == StorageKind.ZeroFill) destination[..n].Clear();
            else document.Read(checked(PreferredBase + offset), n).CopyTo(destination);
            offset += (ulong)n;
            destination = destination[n..];
        }
    }
    public ulong ReadUnsigned(ulong offset, int width)
    {
        if (width is not (1 or 2 or 4 or 8)) throw new ArgumentOutOfRangeException(nameof(width));
        Span<byte> data = stackalloc byte[8];
        ReadBytes(offset, data[..width]);
        ulong result = 0;
        for (var i = 0; i < width; i++) result |= (ulong)data[i] << (8 * i);
        return result;
    }
    public PointerTarget ReadPointer(ulong offset)
    {
        if (offset > ulong.MaxValue - 8) throw new InvalidDataException("指针读取地址溢出");
        // 找第一个起点不小于槽末尾的记录；前缀最大末尾覆盖任意嵌套重叠。
        int low = 0, high = document.Relocations.Count;
        while (low < high)
        {
            var mid = low + (high - low) / 2;
            if (Offset(document.Relocations[mid].Address) < offset + 8) low = mid + 1;
            else high = mid;
        }
        var last = low - 1;
        if (last >= 0 && relocationEnds[last] > offset)
        {
            var r = Relocations[last];
            if (r.Offset != offset || (last > 0 && relocationEnds[last - 1] > offset))
                return new PointerTarget.Unknown("指针读取与重定位部分重叠");
            return r.Kind == RelocationKind.Pointer && r.Width == PointerWidth ? r.Target : new PointerTarget.Unknown("该位置不是静态指针重定位");
        }
        var raw = ReadUnsigned(offset, PointerWidth);
        if (raw == 0) return new PointerTarget.Null();
        return document.PositionIndependent || Relocations.Count != 0
            ? new PointerTarget.NotPointer("非零槽没有重定位，不能作为指针") : InternalTarget(raw);
    }
}
