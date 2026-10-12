using System.Buffers.Binary;

namespace Cpp2CS.Native;

public sealed record UnwindBoundary(ulong Start, ulong End, string? Unsupported)
{
    public ulong? Lsda { get; init; }
    public ulong? PersonalitySlot { get; init; }
    public ExceptionRegion[] ExceptionRegions { get; init; } = [];
    // 只报告读取能力；前端是否支持处理器由各语义层决定。
    public static UnwindBoundary Read(ElfImage image, ulong address)
    {
        if (image.SectionAddress(".eh_frame_hdr") is not { } header) return new(address, address, "缺少 .eh_frame_hdr，异常范围未核实");
        var prefix = image.Read(header, 12);
        if (!prefix.AsSpan(0, 4).SequenceEqual(new byte[] { 1, 0x1b, 0x03, 0x3b })) return new(address, address, "未支持的 EH frame header 编码");
        var count = BinaryPrimitives.ReadUInt32LittleEndian(prefix.AsSpan(8));
        long lo = 0, hi = count - 1, found = -1;
        while (lo <= hi)
        {
            var mid = (lo + hi) / 2;
            var pc = Relative(header + 12 + (ulong)mid * 8, header);
            if (pc <= address) { found = mid; lo = mid + 1; } else hi = mid - 1;
        }
        if (found < 0) return new(address, address, "没有覆盖入口的 FDE");
        var entry = header + 12 + (ulong)found * 8;
        var fde = Relative(entry + 4, header);
        var bytes = image.Read(fde, 16);
        var length = BinaryPrimitives.ReadUInt32LittleEndian(bytes);
        if (length < 12 || length == uint.MaxValue) return new(address, address, "不支持的 FDE 长度");
        var cie = checked(fde + 4 - BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(4)));
        var cieLength = BinaryPrimitives.ReadUInt32LittleEndian(image.Read(cie, 4));
        if (cieLength > 4096) return new(address, address, "CIE 超出支持范围");
        var data = image.Read(cie, checked((int)cieLength + 4));
        if (BinaryPrimitives.ReadUInt32LittleEndian(data.AsSpan(4)) != 0 || data[8] != 1) return new(address, address, "不支持的 CIE 版本");
        var end = Array.IndexOf(data, (byte)0, 9);
        if (end < 0) return new(address, address, "无效 CIE 增强字符串");
        var augmentation = System.Text.Encoding.ASCII.GetString(data, 9, end - 9);
        if (augmentation is not ("zR" or "zPLR")) return new(address, address, $"CIE {augmentation} 含有尚未解析的异常增强信息");
        var offset = end + 1;
        SkipLeb(); SkipLeb(); SkipLeb();
        var augmentationSize = data[offset++];
        byte lsdaEncoding = 0xff;
        ulong? personalitySlot = null;
        if (augmentation == "zPLR")
        {
            var personalityEncoding = data[offset++];
            if (augmentationSize != 11 || personalityEncoding != 0x9c) return new(address, address, "不支持的 personality 编码");
            personalitySlot = checked((ulong)((long)cie + offset + BinaryPrimitives.ReadInt64LittleEndian(data.AsSpan(offset))));
            offset += 8;
            lsdaEncoding = data[offset++];
            if (lsdaEncoding != 0x1c) return new(address, address, "不支持的 LSDA 指针编码");
        }
        else if (augmentationSize != 1) return new(address, address, "不支持的 CIE 增强长度");
        if (data[offset] != 0x1b) return new(address, address, "不支持的 FDE 指针编码");
        var start = checked((ulong)((long)fde + 8 + BinaryPrimitives.ReadInt32LittleEndian(bytes.AsSpan(8))));
        var range = BinaryPrimitives.ReadUInt32LittleEndian(bytes.AsSpan(12));
        if (address != start || range == 0) return new(start, start + range, "入口不是 FDE 起点或范围无效");
        if (lsdaEncoding != 0xff)
        {
            var augmentationBytes = image.Read(fde + 16, 9);
            if (augmentationBytes[0] != 8) return new(start, start + range, "不支持的 FDE LSDA 增强长度");
            var lsda = checked((ulong)((long)fde + 17 + BinaryPrimitives.ReadInt64LittleEndian(augmentationBytes.AsSpan(1))));
            var regions = ExceptionTable.Read(image, lsda, start, start + range);
            return new(start, start + range, null) { Lsda = lsda, ExceptionRegions = regions, PersonalitySlot = personalitySlot };
        }
        return new(start, checked(start + range), null);
        ulong Relative(ulong at, ulong origin) => checked((ulong)((long)origin + BinaryPrimitives.ReadInt32LittleEndian(image.Read(at, 4))));
        void SkipLeb()
        {
            var n = 0;
            while (offset < data.Length && (data[offset++] & 0x80) != 0) if (++n > 9) throw new InvalidDataException("LEB128 超出范围");
        }
    }
}
