using System.Buffers.Binary;
using System.Security.Cryptography;
using Cpp2CS.Input;
using Cpp2CS.Facts;
using Cpp2CS.Spec.Runtime;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.ForwardCheck;


/// <summary>按 FDE 划界。A64 位置字段的含义取自 Arm DDI 0487；不能解释的数据引用留作不可比较。</summary>
internal sealed class FingerprintImage(Elf64 elf, byte[] file, UnwindIndex unwind)
{
    private readonly ElfSection[] data = elf.Sections.Where(s => (s.Flags & 6) == 2 && s.Size > 0).ToArray();
    private readonly ElfSegment[] relro = elf.Segments.Where(s => s.Type == 0x6474e552).ToArray();
    private readonly ulong[] relocated = elf.Relocations.Select(r => r.Address).Order().ToArray();
    public const string AndroidArm64 = "android-arm64-v8a";
    public string? Target => elf.Machine == 183 && elf.Sections.Any(s =>
        s.Name == ".note.android.ident" && s.Type == 7 && s.Size >= 24 &&
        BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan((int)s.Offset)) == 8 &&
        BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan((int)s.Offset + 8)) == 1 &&
        file.AsSpan((int)s.Offset + 12, 8).SequenceEqual("Android\0"u8)) ? AndroidArm64 : null;

    private static bool Inside(ulong address, ulong start, ulong size) => address >= start && address - start < size;
    private static string Hash(ReadOnlySpan<byte> bytes) => Convert.ToHexString(SHA256.HashData(bytes));

    private FingerprintReference? Reference(int offset, ulong address, int width)
    {
        var section = Array.Find(data, s => Inside(address, s.Address, s.Size));
        if (section == null || (ulong)width > section.Size - (address - section.Address)) return null;
        if ((section.Flags & 1) != 0)
        {
            if (relro.Any(s => Inside(address, s.Address, s.MemorySize))) return null;
            return new(offset, ReferenceKind.Writable, address);
        }
        if (section.Type != 1) return null;
        int delta = checked((int)(address - section.Address));
        var bytes = file.AsSpan((int)section.Offset, (int)section.Size);
        ulong start = address;
        int length = width;
        if (width == 0)
        {
            // 没有读取宽度时，只有节声明的字符串元素能按终止符划界。
            if ((section.Flags & 0x30) == 0x30 && section.EntrySize == 1)
            {
                int end = bytes[delta..].IndexOf((byte)0);
                if (end < 0) return null;
                length = end + 1;
            }
            else return null;
        }
        int i = Array.BinarySearch(relocated, start >= 7 ? start - 7 : 0);
        if (i < 0) i = ~i;
        if (i < relocated.Length && relocated[i] < start + (uint)length) return null;
        return new(offset, ReferenceKind.ReadOnly, 0, Hash(bytes.Slice(delta, length)));
    }

    public FingerprintBody Read(Frame frame, IReadOnlySet<ulong> entries)
    {
        int length = checked((int)(frame.End - frame.Start));
        if (length % 4 != 0 || elf.FileOffset(frame.Start, (ulong)length) is not int at)
            return new(0, Hash([]), [], false);
        byte[] body = file.AsSpan(at, length).ToArray();
        var references = new List<FingerprintReference>();
        var pairs = new HashSet<int>();
        var heads = new HashSet<int>();
        bool indirect = false, comparable = true;
        uint Word(int pos) => BinaryPrimitives.ReadUInt32LittleEndian(body.AsSpan(pos));
        void Mask(int pos, uint mask) => BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(pos), Word(pos) & ~mask);
        bool Data(int pos, ulong address, int width)
        {
            if (width == 0 && entries.Contains(address))
            {
                references.Add(new(pos, ReferenceKind.Code, address));
                return true;
            }
            if (Reference(pos, address, width) is { } r) { references.Add(r); return true; }
            comparable = false;
            return false;
        }
        for (int pos = 0; pos < length; pos += 4)
        {
            ulong pc = frame.Start + (uint)pos;
            uint w = Word(pos);
            var op = Decoder.Decode(w);
            if (op.Form == Form.BranchRegister) indirect = true;
            if (op.Form is Form.Branch or Form.Call || op.Conditional)
            {
                ulong destination = op.Destination(pc);
                if (Inside(destination, frame.Start, (uint)length)) heads.Add((int)(destination - frame.Start));
                if (op.Form != Form.Call && Inside(destination, frame.Start, (uint)length)) continue;
                references.Add(new(pos, ReferenceKind.Code, destination));
                Mask(pos, op.Form is Form.Call or Form.Branch ? 0x03ffffffu :
                    op.Form == Form.TestBranch ? 0x0007ffe0u : 0x00ffffe0u);
                continue;
            }
            if (op.Form == Form.Address)
            {
                ulong destination = op.Destination(pc);
                if (op.Name == "adrp")
                {
                    if (pos + 4 >= length) { comparable = false; continue; }
                    uint next = Word(pos + 4);
                    var use = Decoder.Decode(next);
                    // 页地址只在紧接的同寄存器覆写中使用；另一入口可能跳过 ADRP 时不可屏蔽低位。
                    if (op.D == 31 || use.N != op.D || use.D != op.D) { comparable = false; continue; }
                    bool add = (next & 0xffc00000) == 0x91000000;
                    bool load = (next & 0x3b000000) == 0x39000000 && use.Form == Form.Memory &&
                        !use.Vector && use.Name.StartsWith("ldr", StringComparison.Ordinal);
                    if (!add && !load) { comparable = false; continue; }
                    destination = checked((destination & ~4095ul) + (ulong)use.Imm);
                    if (!Data(pos, destination, load ? use.Size / 8 : 0)) continue;
                    Mask(pos + 4, 0x003ffc00);
                    pairs.Add(pos + 4);
                }
                else if (!Data(pos, destination, 0)) continue;
                Mask(pos, 0x60ffffe0);
            }
            else if ((w & 0x3b000000) == 0x18000000)
            {
                if (op.Form != Form.Literal || op.Size == 0) { comparable = false; continue; }
                if (!Data(pos, op.Destination(pc), op.Size / 8)) continue;
                Mask(pos, 0x00ffffe0);
            }
        }
        if (pairs.Count != 0 && (indirect || frame.Lsda != 0 || pairs.Overlaps(heads))) comparable = false;
        return new(length, Hash(body), references.ToArray(), comparable);
    }

    /// <summary>仅用于选取要提升的快照。所有间接边也进入候选，是否能展开只由内核回答。</summary>
    public bool MayCallNamed(Frame f, IReadOnlyDictionary<ulong, RuntimeName> names)
    {
        if (elf.FileOffset(f.Start, f.End - f.Start) is not int at) return false;
        for (ulong pc = f.Start; pc + 4 <= f.End; pc += 4, at += 4)
        {
            uint w = BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(at));
            if ((w & 0xffdffc1f) == 0xd61f0000) return true;
            if ((w & 0x7c000000) == 0x14000000 && names.ContainsKey(unchecked(pc + (ulong)((int)(w << 6) >> 4)))) return true;
            if (Decoder.Decode(w) is { Conditional: true } branch && names.ContainsKey(branch.Destination(pc))) return true;
        }
        return false;
    }

    /// <summary>AAELF64 的 PLT 项：读槽与传给动态链接器的槽地址相同，重定位给出导入名。</summary>
    public Dictionary<ulong, string> ImportStubs()
    {
        var plt = new Dictionary<ulong, string>();
        var slots = elf.Relocations.Where(r => r.Type == 1026 && r.Symbol < elf.DynamicSymbols.Count && r.Addend == 0)
            .ToDictionary(r => r.Address, r => elf.DynamicSymbols[(int)r.Symbol].Name);
        if (elf.Sections.SingleOrDefault(s => s.Name == ".plt") is { } section)
            for (int i = 0; i + 16 <= (int)section.Size; i += 4)
            {
                var code = file.AsSpan((int)section.Offset + i, 16);
                uint a = BinaryPrimitives.ReadUInt32LittleEndian(code), l = BinaryPrimitives.ReadUInt32LittleEndian(code[4..]);
                uint d = BinaryPrimitives.ReadUInt32LittleEndian(code[8..]), b = BinaryPrimitives.ReadUInt32LittleEndian(code[12..]);
                if ((a & 0x9f00001f) != 0x90000010 || (l & 0xffc003ff) != 0xf9400211 ||
                    (d & 0xffc003ff) != 0x91000210 || b != 0xd61f0220 || ((l >> 10) & 4095) * 8 != ((d >> 10) & 4095)) continue;
                ulong pc = section.Address + (uint)i;
                ulong slot = (Decoder.Decode(a).Destination(pc) & ~4095ul) + ((d >> 10) & 4095);
                if (slots.TryGetValue(slot, out string? name) && name.Length > 0) plt.Add(pc, name + "@plt");
            }
        return plt;
    }

    /// <summary>每个托管入口的完整 FDE 各清点一次。B 只计指向函数入口或有 JUMP_SLOT 的 PLT 项。</summary>
    public Dictionary<ulong, int> CallsFrom(HashSet<ulong> managed)
    {
        var plt = ImportStubs();
        var counts = new Dictionary<ulong, int>();
        foreach (var f in unwind.Frames)
        {
            if (!managed.Contains(f.Start) || elf.FileOffset(f.Start, f.End - f.Start) is not int at) continue;
            for (ulong pc = f.Start; pc + 4 <= f.End; pc += 4, at += 4)
            {
                uint w = BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(at));
                if ((w & 0x7c000000) != 0x14000000) continue;
                ulong to = unchecked(pc + (ulong)((int)(w << 6) >> 4));
                if (managed.Contains(to)) continue;
                if ((w >> 31) == 0 && (Inside(to, f.Start, f.End - f.Start) ||
                    !plt.ContainsKey(to) && unwind.Find(to)?.Start != to)) continue;
                counts[to] = counts.GetValueOrDefault(to) + 1;
            }
        }
        return counts;
    }
}
