using System.Buffers.Binary;
using Cpp2CS.Image;
using Cpp2CS.Model;

namespace Cpp2CS.Facts;

/// <summary>
/// 运行时 il2cpp_defaults 全局中的 corlib 类指针。该结构位于可写数据的 BSS 尾部，磁盘内容为零，
/// 元数据槽位解码无法识别；但字段按稳定顺序存放标准类型，加载地址的字段偏移可直接映射到托管类型。
/// 基址由代码中的 ADRP 寻址发现：直接物化基址后，读写至少命中三个不同字段；
/// 编译器把基址与偏移折叠为单条 ADRP+LDR/STR 时，同样要求至少命中三个不同字段，避免把无关静态数据当成基址。
/// 字段偏移随 Unity 版本变化，按元数据版本选择三代布局。
/// </summary>
public sealed class RuntimeDefaults
{
    private readonly Dictionary<ulong, TypeDef> types;

    private RuntimeDefaults(ulong baseAddress, Dictionary<ulong, TypeDef> types)
    {
        BaseAddress = baseAddress;
        this.types = types;
    }

    /// <summary>识别出的 il2cpp_defaults 基址；未识别时为 0。</summary>
    public ulong BaseAddress { get; }

    public int Count => types.Count;

    /// <summary>该地址是否是已知字段槽位；是则返回对应的 corlib 类型。</summary>
    public TypeDef? At(ulong address) => types.GetValueOrDefault(address);

    public static RuntimeDefaults Build(ProgramModel model)
    {
        var layout = LayoutFor(model.MetadataVersion);
        var offsets = layout.Select(f => f.Offset).ToArray();
        var (baseAddress, _) = Discover(model, offsets);
        if (baseAddress == 0) return new RuntimeDefaults(0, []);

        var mapped = new Dictionary<ulong, TypeDef>();
        foreach (var (offset, name) in layout)
        {
            if (Name(model, name) is not { } type) continue;
            mapped[baseAddress + (ulong)offset] = type;
        }
        return new RuntimeDefaults(baseAddress, mapped);
    }

    private static TypeDef? Name(ProgramModel model, string fullName) =>
        model.Types.FirstOrDefault(t => t.FullName == fullName && t.DeclaringType is null);

    private static (int Offset, string Type)[] LayoutFor(double version) => version >= 106
        ? VoidPtrLayout
        : version >= 29 ? ModernLayout : LegacyLayout;

    private static readonly (int Offset, string Type)[] LegacyLayout =
    [
        (0x08, "System.Object"), (0x10, "System.Byte"), (0x20, "System.Boolean"), (0x28, "System.SByte"),
        (0x30, "System.Int16"), (0x38, "System.UInt16"), (0x40, "System.Int32"), (0x48, "System.UInt32"),
        (0x50, "System.IntPtr"), (0x58, "System.UIntPtr"), (0x60, "System.Int64"), (0x68, "System.UInt64"),
        (0x70, "System.Single"), (0x78, "System.Double"), (0x80, "System.Char"), (0x88, "System.String"),
        (0x90, "System.Enum"), (0xD8, "System.Type"), (0xE8, "System.Exception"),
        (0x160, "System.TypedReference"), (0x1B0, "System.Attribute"),
    ];

    private static readonly (int Offset, string Type)[] ModernLayout =
    [
        (0x10, "System.Object"), (0x18, "System.Byte"), (0x28, "System.Boolean"), (0x30, "System.SByte"),
        (0x38, "System.Int16"), (0x40, "System.UInt16"), (0x48, "System.Int32"), (0x50, "System.UInt32"),
        (0x58, "System.IntPtr"), (0x60, "System.UIntPtr"), (0x68, "System.Int64"), (0x70, "System.UInt64"),
        (0x78, "System.Single"), (0x80, "System.Double"), (0x88, "System.Char"), (0x90, "System.String"),
        (0x98, "System.Enum"), (0xE0, "System.Type"), (0xF0, "System.Exception"),
        (0x168, "System.TypedReference"), (0x1B8, "System.Attribute"),
    ];

    private static readonly (int Offset, string Type)[] VoidPtrLayout =
    [
        (0x10, "System.Object"), (0x18, "System.Byte"), (0x30, "System.Boolean"), (0x38, "System.SByte"),
        (0x40, "System.Int16"), (0x48, "System.UInt16"), (0x50, "System.Int32"), (0x58, "System.UInt32"),
        (0x60, "System.IntPtr"), (0x68, "System.UIntPtr"), (0x70, "System.Int64"), (0x78, "System.UInt64"),
        (0x80, "System.Single"), (0x88, "System.Double"), (0x90, "System.Char"), (0x98, "System.String"),
        (0xA0, "System.Enum"), (0xE8, "System.Type"), (0xF8, "System.Exception"),
        (0x168, "System.TypedReference"), (0x1B8, "System.Attribute"),
    ];

    private static (ulong Base, HashSet<int> Offsets) Discover(ProgramModel model, int[] offsets)
    {
        // 运行时初始化函数把基址放进被调用方保存寄存器后，隔着若干次调用逐个写字段；
        // 因此先按 ADRP+ADD 物化出的基址跟踪寄存器，再读取/写入其字段。
        var direct = DirectScan(model, offsets);
        var (candidate, matched) = Best(direct, 3);
        if (candidate != 0) return (candidate, matched);
        // 编译器把基址与字段偏移折叠成单条 ADRP+LDR/STR 时没有物化基址，按字段地址反推候选基址。
        return Best(FoldedScan(model, offsets), 3);
    }

    private static Dictionary<ulong, HashSet<int>> DirectScan(ProgramModel model, int[] offsets)
    {
        var votes = new Dictionary<ulong, HashSet<int>>();
        var known = offsets.ToHashSet();
        var bytes = model.Image.Bytes.Span;
        foreach (var range in model.Image.Ranges.Where(r => r.Executable && r.FileSize >= 24))
        {
            if (range.FileOffset < 0 || range.FileOffset > bytes.Length) continue;
            var start = (int)range.FileOffset;
            var length = (int)Math.Min(range.FileSize, (ulong)(bytes.Length - start));
            if (length < 24) continue;
            var code = bytes.Slice(start, length);
            var registers = new Dictionary<int, (ulong Value, bool Base)>();
            for (var i = 0; i + 4 <= code.Length; i += 4)
            {
                var word = BinaryPrimitives.ReadUInt32LittleEndian(code.Slice(i, 4));
                if ((word & 0x9F000000) == 0x90000000)
                {
                    var imm = ((long)((word >> 5) & 0x7FFFF) << 2) | ((word >> 29) & 3);
                    if ((imm & (1L << 20)) != 0) imm -= 1L << 21;
                    var instruction = range.Address + (ulong)i;
                    registers[(int)(word & 31)] = ((instruction & ~0xFFFUL) + (ulong)(imm << 12), false);
                    continue;
                }
                if ((word & 0xFF800000) == 0x91000000)
                {
                    var destination = (int)(word & 31);
                    var source = (int)((word >> 5) & 31);
                    if (registers.TryGetValue(source, out var value))
                        registers[destination] = (value.Value + (ulong)((word >> 10) & 0xFFF), true);
                    else registers.Remove(destination);
                    continue;
                }
                // MOV Xd, Xm 是 ORR Xd, XZR, Xm。
                if ((word & 0xFFE0FFE0) == 0xAA0003E0)
                {
                    var destination = (int)(word & 31);
                    var source = (int)((word >> 16) & 31);
                    if (registers.TryGetValue(source, out var value)) registers[destination] = value;
                    else registers.Remove(destination);
                    continue;
                }
                var access = word & 0xFFC00000;
                if (access is 0xF9400000 or 0xF9000000)
                {
                    var source = (int)((word >> 5) & 31);
                    var offset = (int)(((word >> 10) & 0xFFF) * 8);
                    if (registers.TryGetValue(source, out var address) && address.Base && known.Contains(offset) && Writable(model, address.Value + (ulong)offset))
                    {
                        if (!votes.TryGetValue(address.Value, out var set)) votes[address.Value] = set = [];
                        set.Add(offset);
                    }
                    if (access == 0xF9400000) registers.Remove((int)(word & 31));
                    continue;
                }
                var call = (word & 0xFC000000) == 0x94000000 || (word & 0xFFFFFC1F) == 0xD63F0000;
                var branch = (word & 0xFC000000) == 0x14000000
                    || (word & 0xFFFFFC1F) is 0xD61F0000 or 0xD65F0000
                    || (word & 0xFF000010) == 0x54000000
                    || (word & 0x7E000000) is 0x34000000 or 0x35000000 or 0x36000000 or 0x37000000;
                if (call)
                {
                    for (var register = 0; register <= 18; register++) registers.Remove(register);
                }
                else if (branch)
                {
                    registers.Clear();
                }
            }
        }
        return votes;
    }

    private static Dictionary<ulong, HashSet<int>> FoldedScan(ProgramModel model, int[] offsets)
    {
        var votes = new Dictionary<ulong, HashSet<int>>();
        var bytes = model.Image.Bytes.Span;
        foreach (var range in model.Image.Ranges.Where(r => r.Executable && r.FileSize >= 24))
        {
            if (range.FileOffset < 0 || range.FileOffset > bytes.Length) continue;
            var start = (int)range.FileOffset;
            var length = (int)Math.Min(range.FileSize, (ulong)(bytes.Length - start));
            if (length < 24) continue;
            var code = bytes.Slice(start, length);
            for (var i = 0; i + 24 <= code.Length; i += 4)
            {
                var word = BinaryPrimitives.ReadUInt32LittleEndian(code.Slice(i, 4));
                if ((word & 0x9F000000) != 0x90000000) continue;
                var reg = (int)(word & 31);
                var imm = ((long)((word >> 5) & 0x7FFFF) << 2) | ((word >> 29) & 3);
                if ((imm & (1L << 20)) != 0) imm -= 1L << 21;
                var instruction = range.Address + (ulong)i;
                var page = (instruction & ~0xFFFUL) + (ulong)(imm << 12);
                for (var k = 4; k <= 20; k += 4)
                {
                    var access = BinaryPrimitives.ReadUInt32LittleEndian(code.Slice(i + k, 4));
                    if ((access & 0xFFC00000) is not (0xF9400000 or 0xF9000000) || (int)((access >> 5) & 31) != reg) continue;
                    var field = page + (ulong)(((access >> 10) & 0xFFF) * 8);
                    Vote(model, votes, field, offsets);
                    break;
                }
            }
        }
        return votes;
    }

    private static void Vote(ProgramModel model, Dictionary<ulong, HashSet<int>> votes, ulong loaded, int[] offsets)
    {
        if (!Writable(model, loaded)) return;
        foreach (var offset in offsets)
        {
            if ((ulong)offset >= loaded) continue;
            var candidate = loaded - (ulong)offset;
            if (!Writable(model, candidate)) continue;
            if (!votes.TryGetValue(candidate, out var set)) votes[candidate] = set = [];
            set.Add(offset);
        }
    }

    private static bool Writable(ProgramModel model, ulong address)
    {
        var mapping = model.Image.Resolve(address);
        return mapping.Kind != AddressKind.Unmapped && mapping.Range!.Writable;
    }

    private static (ulong Base, HashSet<int> Offsets) Best(Dictionary<ulong, HashSet<int>> votes, int minimum)
    {
        var best = 0UL;
        var bestOffsets = new HashSet<int>();
        var tied = false;
        foreach (var (candidate, offsets) in votes)
        {
            if (offsets.Count < minimum || offsets.Count < bestOffsets.Count) continue;
            if (offsets.Count > bestOffsets.Count)
            {
                best = candidate;
                bestOffsets = offsets;
                tied = false;
            }
            else if (candidate != best)
            {
                tied = true;
            }
        }
        return tied ? (0, []) : (best, bestOffsets);
    }
}
