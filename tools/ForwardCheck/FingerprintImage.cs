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
    private readonly FingerprintData objects = new(elf, file);
    public const string AndroidArm64 = "android-arm64-v8a";
    public string? Target => elf.Machine == 183 && elf.Sections.Any(s =>
        s.Name == ".note.android.ident" && s.Type == 7 && s.Size >= 24 &&
        BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan((int)s.Offset)) == 8 &&
        BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan((int)s.Offset + 8)) == 1 &&
        file.AsSpan((int)s.Offset + 12, 8).SequenceEqual("Android\0"u8)) ? AndroidArm64 : null;

    private static bool Inside(ulong address, ulong start, ulong size) => address >= start && address - start < size;
    private static string Hash(ReadOnlySpan<byte> bytes) => Convert.ToHexString(SHA256.HashData(bytes));

    public void AddObjectBounds(IEnumerable<(ulong Address, ulong Size)> bounds) => objects.AddBounds(bounds);

    // 页基只在一个基本块内有效。每次读都须给出同一地址，直至覆盖页基或证明它在出口死亡。
    private bool PageUses(Frame frame, int at, int length, int pos, int reg, HashSet<int> heads,
        IReadOnlySet<ulong> entries, List<(int Pos, ulong Address, int Width)> uses)
    {
        if (reg is 18 or 31) return false; // Android 保留 x18，31 不是通用寄存器。
        uint bit = 1u << reg;
        ulong pc = frame.Start + (uint)pos;
        uint Word(int i) => BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(at + i));
        ulong page = Decoder.Decode(Word(pos)).Destination(pc & ~4095ul);
        // 只在本块配对。页基没有被使用者覆写时，后继各路径须在再读之前改写它。
        bool DeadFrom(int next)
        {
            var pending = new Stack<int>();
            var seen = new HashSet<int>();
            pending.Push(next);
            while (pending.TryPop(out int i))
            {
                for (; i < length && seen.Add(i); i += 4)
                {
                    var op = Decoder.Decode(Word(i));
                    if (op.Form is Form.Unknown or Form.BranchRegister || (op.ReadGeneralRegisters & bit) != 0) return false;
                    if ((op.WrittenGeneralRegisters & bit) != 0 || op.Form is Form.Return or Form.Trap) break;
                    if (op.IsCall) return false;
                    if (op.Form == Form.Branch || op.Conditional)
                    {
                        ulong dest = op.Destination(frame.Start + (uint)i);
                        if (Inside(dest, frame.Start, (uint)length)) pending.Push((int)(dest - frame.Start));
                        else if (Abi.RequiredAtTail(reg)) return false;
                        if (!op.Conditional) break;
                    }
                }
                if (i == length) return false;
            }
            return true;
        }
        for (int i = pos + 4; i < length; i += 4)
        {
            if (heads.Contains(i) || entries.Contains(frame.Start + (uint)i)) return uses.Count != 0 && DeadFrom(i);
            uint word = Word(i);
            var ins = Decoder.Decode(word);
            if (ins.Form == Form.Unknown) return false;
            if ((ins.ReadGeneralRegisters & bit) != 0)
            {
                bool add = (word & 0xffc00000) == 0x91000000;
                bool load = (word & 0x3b000000) == 0x39000000 && ins.Form == Form.Memory && ins.Name[0] == 'l';
                if (ins.N != reg || !add && !load) return false;
                ulong address = page + (ulong)ins.Imm;
                if (uses.Count > 0 && address != uses[0].Address) return false;
                uses.Add((i, address, load ? ins.Size / 8 : 0));
            }
            if ((ins.WrittenGeneralRegisters & bit) != 0 || ins.Form is Form.Return or Form.Trap) return uses.Count != 0;
            if (ins.Conditional || ins.IsCall || ins.Form is Form.Branch or Form.BranchRegister)
                return uses.Count != 0 && DeadFrom(i);
        }
        return false;
    }

    public FingerprintBody Read(Frame frame, IReadOnlySet<ulong> entries, Action<int, string>? failure = null)
    {
        int length = checked((int)(frame.End - frame.Start));
        if (length == 0 || length % 4 != 0 || elf.FileOffset(frame.Start, (ulong)length) is not int at)
        {
            failure?.Invoke(0, "代码范围不完整");
            return new(0, Hash([]), [], false);
        }
        byte[] body = file.AsSpan(at, length).ToArray();
        var references = new List<FingerprintReference>();
        bool comparable = true;
        uint Word(int pos) => BinaryPrimitives.ReadUInt32LittleEndian(file.AsSpan(at + pos));
        void Mask(int pos, uint mask) => BinaryPrimitives.WriteUInt32LittleEndian(body.AsSpan(pos), Word(pos) & ~mask);
        bool Data(int pos, ulong address, int width)
        {
            if (objects.Reference(pos, address, width, entries, references)) return true;
            failure?.Invoke(pos, $"数据范围或重定位未核实 0x{address:x}，读取宽度 {width}");
            comparable = false;
            return false;
        }
        var heads = new HashSet<int>();
        bool indirect = false, hasPage = false;
        for (int pos = 0; pos < length; pos += 4)
        {
            var op = Decoder.Decode(Word(pos));
            if (op.Name == "adrp") hasPage = true;
            if (op.Form == Form.BranchRegister || op.Form == Form.Unknown && (Word(pos) & 0xfe000000) == 0xd6000000)
                indirect = true;
            if (op.Form is Form.Branch or Form.Call || op.Conditional)
            {
                ulong dest = op.Destination(frame.Start + (uint)pos);
                if (Inside(dest, frame.Start, (uint)length)) heads.Add((int)(dest - frame.Start));
            }
        }
        if (hasPage && frame.Lsda != 0)
        {
            try
            {
                foreach (var site in unwind.Sites(frame))
                    if (Inside(site.Landing, frame.Start, (uint)length)) heads.Add((int)(site.Landing - frame.Start));
            }
            catch (InvalidDataException e) { comparable = false; failure?.Invoke(0, e.Message); }
        }
        var uses = new List<(int Pos, ulong Address, int Width)>();
        if (indirect && hasPage)
        {
            comparable = false;
            failure?.Invoke(0, "间接跳转的块入口未核实");
        }
        for (int pos = 0; pos < length; pos += 4)
        {
            ulong pc = frame.Start + (uint)pos;
            uint w = Word(pos);
            var op = Decoder.Decode(w);
            if (op.Form is Form.Branch or Form.Call || op.Conditional)
            {
                ulong destination = op.Destination(pc);
                if (op.Form != Form.Call && Inside(destination, frame.Start, (uint)length)) continue;
                references.Add(new(pos, ReferenceKind.Code, destination));
                Mask(pos, op.Form is Form.Call or Form.Branch ? 0x03ffffffu :
                    op.Form == Form.TestBranch ? 0x0007ffe0u : 0x00ffffe0u);
            }
            else if (op.Name == "adrp")
            {
                uses.Clear();
                if (!PageUses(frame, at, length, pos, op.D, heads, entries, uses))
                {
                    failure?.Invoke(pos, $"页基 x{op.D} 的块内使用未闭合");
                    comparable = false;
                    continue;
                }
                foreach (var use in uses)
                    if (Data(use.Pos, use.Address, use.Width)) Mask(use.Pos, 0x003ffc00);
                Mask(pos, 0x60ffffe0);
            }
            else if (op.Form == Form.Address)
            {
                if (Data(pos, op.Destination(pc), 0)) Mask(pos, 0x60ffffe0);
            }
            else if ((w & 0x3b000000) == 0x18000000)
            {
                if (op.Form != Form.Literal || op.Size == 0)
                { failure?.Invoke(pos, "文字池读取宽度未知"); comparable = false; continue; }
                if (Data(pos, op.Destination(pc), op.Size / 8)) Mask(pos, 0x00ffffe0);
            }
        }
        return new(length, Hash(body), [.. references.OrderBy(r => r.Offset)], comparable);
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
