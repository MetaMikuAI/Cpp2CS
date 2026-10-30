using System.Buffers.Binary;
using System.Text;

namespace Cpp2CS.Image;

/// <summary>
/// 全量函数边界表。一次构建，之后按地址查询。
/// 只接受展开表（FDE / RUNTIME_FUNCTION）给出的边界；符号候选不作为已核实边界。
/// </summary>
public sealed class FunctionTable
{
    private readonly FunctionRange[] ranges;

    private FunctionTable(FunctionRange[] ranges, string source)
    {
        this.ranges = ranges;
        Source = source;
    }

    public string Source { get; }

    public IReadOnlyList<FunctionRange> Ranges => ranges;

    /// <summary>构建过程中跳过的 FDE/RUNTIME_FUNCTION 条目数及其原因，用于报告边界覆盖缺口。</summary>
    public IReadOnlyList<string> Skipped { get; private init; } = [];

    public static FunctionTable Build(ImageDocument image)
    {
        if (image.Architecture == Cpp2CS.Model.Architecture.Arm64) return Arm64(image);
        return X64(image);
    }

    /// <summary>返回覆盖 address 的函数范围；没有已核实边界时返回 null。</summary>
    public FunctionRange? At(ulong address)
    {
        var low = 0;
        var high = ranges.Length - 1;
        while (low <= high)
        {
            var middle = low + (high - low) / 2;
            var range = ranges[middle];
            if (address < range.Start) { high = middle - 1; continue; }
            if (address >= range.End) { low = middle + 1; continue; }
            return range;
        }
        return null;
    }

    public FunctionRange? Next(ulong address)
    {
        var low = 0;
        var high = ranges.Length - 1;
        var found = -1;
        while (low <= high)
        {
            var middle = low + (high - low) / 2;
            if (ranges[middle].Start > address) { found = middle; high = middle - 1; }
            else low = middle + 1;
        }
        return found < 0 ? null : ranges[found];
    }

    private static FunctionTable Arm64(ImageDocument image)
    {
        if (image.EhFrameHeader is not { } header)
            throw new InvalidDataException("ELF 没有 PT_GNU_EH_FRAME；无法核实 ARM64 函数边界");
        var prefix = image.Read(header, 12);
        if (!prefix[..4].SequenceEqual(new byte[] { 1, 0x1b, 0x03, 0x3b }))
            throw new NotSupportedException($"未支持的 .eh_frame_hdr 编码：{Convert.ToHexString(prefix[..4])}");
        var count = BinaryPrimitives.ReadUInt32LittleEndian(prefix[8..]);
        var entries = image.Read(header + 12, checked((int)count * 8));
        var ranges = new List<FunctionRange>(checked((int)count));
        var skipped = new List<string>();
        ulong? previousStart = null;
        for (var i = 0; i < count; i++)
        {
            var entry = header + 12 + (ulong)i * 8;
            var start = PcRelative(image, entry, header);
            var fde = PcRelative(image, entry + 4, header);
            if (previousStart is { } lower && start < lower)
                throw new InvalidDataException($".eh_frame_hdr 二分表未按 PC 升序：0x{start:x} < 0x{lower:x}");
            previousStart = start;
            ParseFde(image, start, fde, ranges, skipped);
        }
        var ordered = ranges.OrderBy(r => r.Start).ToArray();
        for (var i = 1; i < ordered.Length; i++)
            if (ordered[i].Start < ordered[i - 1].End)
                throw new InvalidDataException($"FDE 范围重叠：{ordered[i - 1].Describe()} 与 {ordered[i].Describe()}");
        return new(ordered, ".eh_frame_hdr") { Skipped = skipped };
    }

    // 单个 FDE：只接受 [start, start+range) 与 CIE 增强信息均已核实的条目。
    private static void ParseFde(ImageDocument image, ulong start, ulong fde, List<FunctionRange> ranges, List<string> skipped)
    {
        var head = image.Read(fde, 12);
        var length = BinaryPrimitives.ReadUInt32LittleEndian(head);
        if (length is 0 or 0xffffffff) { skipped.Add($"0x{fde:x}: 不支持的 FDE 长度 {length}"); return; }
        var ciePointer = BinaryPrimitives.ReadUInt32LittleEndian(head[4..]);
        var cie = checked(fde + 4 - ciePointer);
        var cieLength = BinaryPrimitives.ReadUInt32LittleEndian(image.Read(cie, 4));
        if (cieLength is 0 or > 4096) { skipped.Add($"0x{fde:x}: CIE 长度 {cieLength} 不可用"); return; }
        var cieData = image.Read(cie, checked((int)cieLength + 4));
        if (BinaryPrimitives.ReadUInt32LittleEndian(cieData[4..]) != 0 || cieData[8] != 1)
        {
            skipped.Add($"0x{fde:x}: 不支持的 CIE 版本 {BinaryPrimitives.ReadUInt32LittleEndian(cieData[4..])}/{cieData[8]}");
            return;
        }
        var cieEnd = Array.IndexOf(cieData.ToArray(), (byte)0, 9);
        if (cieEnd < 0) { skipped.Add($"0x{fde:x}: CIE 增强字符串未终止"); return; }
        var augmentation = Encoding.ASCII.GetString(cieData[9..cieEnd]);
        if (augmentation is not ("zR" or "zPLR"))
        {
            skipped.Add($"0x{fde:x}: CIE 增强 {augmentation} 含有未解析的异常信息");
            return;
        }
        var offset = cieEnd + 1;
        SkipLeb(cieData, ref offset);
        SkipLeb(cieData, ref offset);
        SkipLeb(cieData, ref offset);
        var augmentationSize = cieData[offset++];
        byte lsdaEncoding = 0xff;
        if (augmentation == "zPLR")
        {
            var personalityEncoding = cieData[offset];
            if (augmentationSize != 11 || personalityEncoding != 0x9c)
            {
                skipped.Add($"0x{fde:x}: 不支持的 personality 编码 0x{personalityEncoding:x2}/{augmentationSize}");
                return;
            }
            offset += 9;
            lsdaEncoding = cieData[offset++];
            if (lsdaEncoding != 0x1c) { skipped.Add($"0x{fde:x}: 不支持的 LSDA 编码 0x{lsdaEncoding:x2}"); return; }
        }
        else if (augmentationSize != 1) { skipped.Add($"0x{fde:x}: 不支持的 CIE 增强长度 {augmentationSize}"); return; }
        if (cieData[offset] != 0x1b) { skipped.Add($"0x{fde:x}: 不支持的 FDE 指针编码 0x{cieData[offset]:x2}"); return; }
        var declaredStart = checked((ulong)((long)fde + 8 + image.ReadI32(fde + 8)));
        var range = BinaryPrimitives.ReadUInt32LittleEndian(image.Read(fde + 12, 4));
        if (declaredStart != start) { skipped.Add($"0x{fde:x}: FDE 起点 0x{declaredStart:x} 与二分表 0x{start:x} 不一致"); return; }
        if (range == 0) { skipped.Add($"0x{fde:x}: FDE 范围为零"); return; }
        if (!image.IsExecutable(start))
        {
            skipped.Add($"0x{fde:x}: 起点 0x{start:x} 不在可执行映射内");
            return;
        }
        if (lsdaEncoding == 0xff)
        {
            ranges.Add(new(start, checked(start + range), BoundaryEvidence.EhFrame, null));
            return;
        }
        var augmentationBytes = image.Read(fde + 16, 9);
        if (augmentationBytes[0] != 8) { skipped.Add($"0x{fde:x}: 不支持的 FDE LSDA 增强长度 {augmentationBytes[0]}"); return; }
        var lsda = checked((ulong)((long)fde + 17 + BinaryPrimitives.ReadInt64LittleEndian(augmentationBytes[1..])));
        var regions = ExceptionTable.Read(image, lsda, start, checked(start + range));
        ranges.Add(new(start, checked(start + range), BoundaryEvidence.EhFrame, null) { ExceptionRegions = regions });
    }

    private static void SkipLeb(ReadOnlySpan<byte> data, ref int offset)
    {
        var count = 0;
        while (offset < data.Length && (data[offset++] & 0x80) != 0)
            if (++count > 9)
                throw new InvalidDataException("CIE 中的 LEB128 超出范围");
    }

    private static ulong PcRelative(ImageDocument image, ulong at, ulong origin) =>
        checked((ulong)((long)origin + image.ReadI32(at)));

    private sealed record PdataEntry(ulong Start, ulong End, ulong Unwind);

    private static FunctionTable X64(ImageDocument image)
    {
        if (image.ExceptionDirectory is not { } directory)
            throw new InvalidDataException("PE 没有异常目录（.pdata）；无法核实 x64 函数边界");
        if (directory.Size % 12 != 0) throw new InvalidDataException($"PE 异常目录长度 {directory.Size} 不是 12 的倍数");
        var count = checked((int)(directory.Size / 12));
        var raw = image.Read(directory.Address, checked(count * 12));
        var entries = new List<PdataEntry>(count);
        var skipped = new List<string>();
        for (var i = 0; i < count; i++)
        {
            var entry = Entry(image, raw.Slice(i * 12, 12));
            if (entries.Count > 0 && entry.Start < entries[^1].Start)
                throw new InvalidDataException($".pdata 未按入口升序：0x{entry.Start:x} < 0x{entries[^1].Start:x}");
            if (entry.End <= entry.Start) { skipped.Add($"0x{entry.Start:x}: 范围终点 0x{entry.End:x} 非正向"); continue; }
            if (!image.IsExecutable(entry.Start)) { skipped.Add($"0x{entry.Start:x}: 入口不在可执行映射内"); continue; }
            if ((entry.Unwind & 1) != 0) { skipped.Add($"0x{entry.Start:x}: 间接 UNWIND_INFO 未支持"); continue; }
            if (image.Resolve(entry.Unwind).Kind != AddressKind.FileBacked)
            {
                skipped.Add($"0x{entry.Start:x}: UNWIND_INFO 0x{entry.Unwind:x} 未映射");
                continue;
            }
            entries.Add(entry);
        }
        for (var i = 1; i < entries.Count; i++)
            if (entries[i].Start < entries[i - 1].End)
                throw new InvalidDataException($".pdata 范围重叠：0x{entries[i - 1].Start:x}..0x{entries[i - 1].End:x} 与 0x{entries[i].Start:x}");

        // UNWIND_INFO 第 0 字节：低 3 位版本，高 5 位标志（1 EHANDLER，2 UHANDLER，4 CHAININFO）。
        // 展开码数组按偶数个槽位对齐，其后是处理例程 RVA，或者（CHAININFO 时）上级 RUNTIME_FUNCTION。
        // 链式条目是同一函数的后续片段，不能当作独立函数入口。
        var byStart = entries.ToDictionary(e => e.Start);
        var roots = new List<PdataEntry>();
        var fragments = new Dictionary<ulong, List<FunctionRange>>();
        foreach (var entry in entries)
        {
            var root = entry;
            for (var depth = 0; (Flags(image, root.Unwind) & 4) != 0; depth++)
            {
                if (depth > 32) throw new InvalidDataException($"0x{entry.Start:x}: UNWIND_INFO 链过深或成环");
                var parent = Entry(image, image.Read(Trailer(image, root.Unwind), 12));
                if (!byStart.TryGetValue(parent.Start, out var listed) || listed != parent)
                    throw new InvalidDataException($"0x{root.Start:x}: 链式 UNWIND_INFO 指向的 0x{parent.Start:x} 不是 .pdata 条目");
                root = listed;
            }
            if (root == entry) { roots.Add(entry); continue; }
            if (!fragments.TryGetValue(root.Start, out var list)) fragments[root.Start] = list = [];
            list.Add(new(entry.Start, entry.End, BoundaryEvidence.Pdata, "chained"));
        }

        var ranges = new FunctionRange[roots.Count];
        for (var i = 0; i < roots.Count; i++)
        {
            var root = roots[i];
            ulong? handler = null;
            ulong? data = null;
            if ((Flags(image, root.Unwind) & 3) != 0)
            {
                var trailer = Trailer(image, root.Unwind);
                handler = checked(image.PreferredBase + image.ReadU32(trailer));
                data = trailer + 4;
                if (!image.IsExecutable(handler.Value))
                    throw new InvalidDataException($"0x{root.Start:x}: 异常处理例程 0x{handler:x} 不在可执行映射内");
            }
            ranges[i] = new(root.Start, root.End, BoundaryEvidence.Pdata, null)
            {
                Fragments = fragments.TryGetValue(root.Start, out var list) ? list.ToArray() : [],
                Handler = handler,
                HandlerData = data,
            };
        }
        return new(ranges, ".pdata") { Skipped = skipped };
    }

    private static PdataEntry Entry(ImageDocument image, ReadOnlySpan<byte> raw) => new(
        checked(image.PreferredBase + BinaryPrimitives.ReadUInt32LittleEndian(raw)),
        checked(image.PreferredBase + BinaryPrimitives.ReadUInt32LittleEndian(raw[4..])),
        checked(image.PreferredBase + BinaryPrimitives.ReadUInt32LittleEndian(raw[8..])));

    private static int Flags(ImageDocument image, ulong unwind)
    {
        var header = image.Read(unwind, 4);
        if ((header[0] & 7) is not (1 or 2)) throw new NotSupportedException($"UNWIND_INFO 0x{unwind:x} 版本 {header[0] & 7} 未支持");
        return header[0] >> 3;
    }

    private static ulong Trailer(ImageDocument image, ulong unwind) =>
        checked(unwind + 4 + (ulong)((image.Read(unwind, 4)[2] + 1) & ~1) * 2);
}
