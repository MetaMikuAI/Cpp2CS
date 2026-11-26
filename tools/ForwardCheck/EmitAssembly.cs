using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using AsmResolver;
using AsmResolver.PE;
using AsmResolver.PE.DotNet.Metadata;
using AsmResolver.PE.DotNet.Metadata.Tables;
using AsmResolver.PE.File;
using Cpp2CS.Output;
using SrmTable = System.Reflection.Metadata.Ecma335.TableIndex;
using PeTable = AsmResolver.PE.DotNet.Metadata.Tables.TableIndex;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>沿用原模块的表行、堆索引与节地址，只追加方法体、局部签名和新的元数据目录。</summary>
internal sealed class EmitAssembly
{
    private readonly PEFile file;
    private readonly Module source;
    private readonly MetadataDirectory directory;
    private readonly TablesStream tables;
    private readonly BlobStream oldBlobs;
    private readonly BlobBuilder extraBlobs = new();
    private readonly Dictionary<string, int> signatures = [];
    private readonly SegmentBuilder addition = new();
    public Dictionary<int, CilMethodBody> Replacements { get; } = [];

    public EmitAssembly(Module source)
    {
        this.source = source;
        file = PEFile.FromBytes(source.Pe.GetEntireImage().GetContent().ToArray());
        directory = PEImage.FromFile(file).DotNetDirectory!.Metadata!;
        tables = directory.GetStream<TablesStream>();
        oldBlobs = directory.GetStream<BlobStream>();
        var rows = tables.GetTable<StandAloneSignatureRow>();
        for (int i = 0; i < rows.Count; i++)
            if (oldBlobs.GetBlobByIndex(rows[i].Signature) is { } bytes)
                signatures.TryAdd(Convert.ToHexString(bytes), 0x11000001 + i);
    }

    public int RegisterLocals(ImmutableArray<byte> signature)
    {
        string key = Convert.ToHexString(signature.AsSpan());
        if (signatures.TryGetValue(key, out int token)) return token;
        if (!oldBlobs.TryFindBlobIndex(signature.ToArray(), out uint offset))
        {
            offset = checked(oldBlobs.GetPhysicalSize() + (uint)extraBlobs.Count);
            extraBlobs.WriteCompressedInteger(signature.Length);
            extraBlobs.WriteBytes(signature);
        }
        var rows = tables.GetTable<StandAloneSignatureRow>();
        rows.Add(new(offset));
        return signatures[key] = 0x11000000 | rows.Count;
    }

    public void Replace(int token, CilMethodBody body)
    {
        Replacements.Add(token, body);
        var segment = new DataSegment(body.Bytes.ToArray());
        addition.Add(segment, 4);
        var methods = tables.GetTable<MethodDefinitionRow>();
        uint rid = (uint)token & 0xffffff;
        var row = methods.GetByRid(rid);
        row.Body = segment.ToReference();
        methods.SetByRid(rid, row);
    }

    public void Write(string path)
    {
        if (extraBlobs.Count > 0)
        {
            var blobs = new BlobBuilder();
            blobs.WriteBytes(oldBlobs.CreateReader().ReadToEnd());
            blobs.LinkSuffix(extraBlobs);
            blobs.Align(4);
            directory.Streams[directory.Streams.IndexOf(oldBlobs)] = new SerializedBlobStream(blobs.ToArray());
            if (blobs.Count > ushort.MaxValue) tables.BlobIndexSize = IndexSize.Long;
        }
        // Blob 堆或 StandAloneSig 表增长可能使其他表的索引列变宽。
        uint Width(ColumnLayout c) => c.Type switch
        {
            ColumnType.Blob => (uint)tables.BlobIndexSize,
            ColumnType.StandAloneSig => (uint)tables.GetTableIndexSize(PeTable.StandAloneSig),
            ColumnType.HasCustomAttribute => (uint)tables.GetIndexEncoder(AsmResolver.PE.DotNet.Metadata.Tables.CodedIndex.HasCustomAttribute).IndexSize,
            ColumnType.HasCustomDebugInformation => (uint)tables.GetIndexEncoder(AsmResolver.PE.DotNet.Metadata.Tables.CodedIndex.HasCustomDebugInformation).IndexSize,
            _ => c.Size,
        };
        foreach (var index in Enum.GetValues<SrmTable>())
        {
            if (tables.GetTableRowCount((PeTable)index) == 0) continue;
            var table = tables.GetTable((PeTable)index);
            var columns = table.Layout.Columns;
            if (columns.All(c => c.Size == Width(c))) continue;
            _ = table[0]; // 先按原行宽读取延迟加载的行。
            table.UpdateTableLayout(new([.. columns.Select(c => new ColumnLayout(c.Name, c.Type, Width(c)))]));
        }
        addition.Add(directory, 4);

        // 扩展尾节，原来的 RVA 和文件偏移保持有效（含调试目录中的文件指针）。
        var last = file.Sections[^1];
        var content = new SegmentBuilder();
        var header = source.Pe.PEHeaders.SectionHeaders[^1];
        var original = new byte[Math.Max(header.VirtualSize, header.SizeOfRawData)];
        source.Pe.GetEntireImage().GetContent(header.PointerToRawData, header.SizeOfRawData).CopyTo(original);
        content.Add(new DataSegment(original));
        content.Add(addition, 4);
        last.Contents = content;
        last.IsMemoryDiscardable = false;
        last.IsMemoryRead = true;
        file.UpdateHeaders();
        uint rawGrowth = checked(last.CreateHeader().SizeOfRawData - (uint)header.SizeOfRawData);
        if (last.IsContentInitializedData) file.OptionalHeader.SizeOfInitializedData = checked(file.OptionalHeader.SizeOfInitializedData + rawGrowth);
        if (last.IsContentCode) file.OptionalHeader.SizeOfCode = checked(file.OptionalHeader.SizeOfCode + rawGrowth);

        using var stream = new MemoryStream();
        file.Write(stream);
        for (int i = 0; i < file.Sections.Count; i++)
        {
            var previous = source.Pe.PEHeaders.SectionHeaders[i];
            if (file.Sections[i].Rva != previous.VirtualAddress || file.Sections[i].Offset != (uint)previous.PointerToRawData)
                throw new InvalidDataException($"追加写出会移动原有节 {previous.Name}");
        }
        // II.25.3.3：CLI 头偏移 8 是元数据目录的 RVA 和大小。
        var entry = stream.GetBuffer().AsSpan(source.Pe.PEHeaders.CorHeaderStartOffset + 8);
        BinaryPrimitives.WriteUInt32LittleEndian(entry, directory.Rva);
        BinaryPrimitives.WriteUInt32LittleEndian(entry[4..], directory.GetPhysicalSize());
        using var output = new FileStream(path, FileMode.CreateNew, FileAccess.Write);
        stream.WriteTo(output);
    }

    /// <summary>核对原有堆和每个元数据单元格。允许追加签名及其 blob，替换的 MethodDef 只允许改 RVA。</summary>
    public void CheckMetadata(Module copy)
    {
        var before = source.Pe.GetMetadata();
        var after = copy.Pe.GetMetadata();
        foreach (var heap in Enum.GetValues<HeapIndex>())
        {
            int size = source.Md.GetHeapSize(heap);
            int newSize = copy.Md.GetHeapSize(heap);
            if (newSize < size || (heap != HeapIndex.Blob && newSize != size))
                throw new InvalidDataException($"{heap} 堆长度改变");
            if (size == 0) continue;
            var a = before.GetContent(source.Md.GetHeapMetadataOffset(heap), size);
            var b = after.GetContent(copy.Md.GetHeapMetadataOffset(heap), size);
            if (!a.AsSpan().SequenceEqual(b.AsSpan())) throw new InvalidDataException($"{heap} 堆的原有字节改变");
        }
        static TablesStream Read(Module m) => PEImage.FromBytes(m.Pe.GetEntireImage().GetContent().ToArray()).DotNetDirectory!.Metadata!.GetStream<TablesStream>();
        var original = Read(source);
        var written = Read(copy);
        foreach (var index in Enum.GetValues<SrmTable>())
        {
            var table = (PeTable)index;
            int count = source.Md.GetTableRowCount(index);
            int expected = index == SrmTable.StandAloneSig ? tables.GetTable<StandAloneSignatureRow>().Count : count;
            if (copy.Md.GetTableRowCount(index) != expected) throw new InvalidDataException($"{index} 表行数不符");
            if (count == 0) continue;
            var a = original.GetTable(table);
            var b = written.GetTable(table);
            for (int i = 0; i < count; i++)
            {
                int first = index == SrmTable.MethodDef && Replacements.ContainsKey(0x06000001 + i) ? 1 : 0;
                var left = a[i];
                var right = b[i];
                for (int c = first; c < left.Count; c++)
                    if (left[c] != right[c]) throw new InvalidDataException($"{index} 第 {i + 1} 行第 {c} 列改变");
            }
        }
    }
}
