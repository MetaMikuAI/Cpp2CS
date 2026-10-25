using System.Buffers.Binary;
using Cpp2CS.Functions;
using Cpp2CS.Images;

namespace Cpp2CS.Facts;

/// <summary>代码所在区域。托管生成代码在 il2cpp 节；运行时（libil2cpp、libc++ 等）在 .text。</summary>
public enum CodeRegion { Managed, Runtime, Plt, Other }

/// <summary>一个函数的代码范围与边界依据。</summary>
public sealed record CodeFunction(ulong Start, ulong End, CodeRegion Region, BoundaryEvidence Evidence)
{
    public ulong Size => End - Start;
    public bool Contains(ulong address) => address >= Start && address < End;
    /// <summary>LSDA 给出的 call-site 区间（落地块只能经由展开到达）。</summary>
    public ExceptionRegion[] ExceptionRegions { get; init; } = [];
    /// <summary>PLT 桩所引用的动态符号名。</summary>
    public string? Import { get; init; }
}

/// <summary>
/// Cortex-A53 勘误 843419 补丁：Site 处原指令被链接器换成 B Stub，Stub 执行 Original 后跳回 Site+4。
/// AdrpPageOffset：Site 之前 1–4 条内最近一条 ADRP 的页内偏移；没有 ADRP 为 null。
/// 本映像中这一偏移集中在 0xFF8/0xFFC（勘误条件本身）与 0x020/0x024（同一条件整体后移 0x28 字节）两簇。
/// </summary>
public sealed record ErratumPatch(ulong Site, ulong Stub, uint Original, int? AdrpPageOffset);

/// <summary>可执行节中不属于任何函数的区间及其归类。</summary>
public sealed record CodeGap(ulong Start, ulong End, string Kind);

/// <summary>
/// 全量代码地图：函数边界（FDE 为主）、勘误补丁、PLT 桩、无 FDE 的被引用入口、可执行节空隙。
/// 读取指令一律经 <see cref="Word"/>，它对勘误补丁位置返回原指令，使函数体在逻辑上恢复为链接前的指令序列。
/// </summary>
public sealed class CodeMap
{
    private readonly (ImageSection Section, ReadOnlyMemory<byte> Bytes)[] code;
    private readonly CodeFunction[] functions;
    private readonly ulong[] starts;
    private readonly Dictionary<ulong, ErratumPatch> patches;

    public ImageDocument Image { get; }
    public IReadOnlyList<CodeFunction> Functions => functions;
    public IReadOnlyDictionary<ulong, ErratumPatch> Patches => patches;
    public IReadOnlyList<CodeGap> Gaps { get; }
    public IReadOnlyList<string> FdeSkipped { get; }
    /// <summary>没有 FDE 但被引用的入口：入口地址 → 引用来源（"bl"、"b"、"adrp+add"、"adr"、"reloc"）。</summary>
    public IReadOnlyDictionary<ulong, string> ReferencedWithoutFde { get; }

    private CodeMap(ImageDocument image, (ImageSection, ReadOnlyMemory<byte>)[] code, CodeFunction[] functions,
        Dictionary<ulong, ErratumPatch> patches, CodeGap[] gaps, IReadOnlyList<string> skipped, Dictionary<ulong, string> referenced)
    {
        Image = image;
        this.code = code;
        this.functions = functions;
        starts = functions.Select(f => f.Start).ToArray();
        this.patches = patches;
        Gaps = gaps;
        FdeSkipped = skipped;
        ReferencedWithoutFde = referenced;
    }

    public IReadOnlyList<(ImageSection Section, ReadOnlyMemory<byte> Bytes)> CodeSections => code;

    /// <summary>覆盖 address 的函数序号；不在任何函数内返回 -1。</summary>
    public int IndexOf(ulong address)
    {
        var i = Array.BinarySearch(starts, address);
        if (i < 0) i = ~i - 1;
        return i >= 0 && functions[i].Contains(address) ? i : -1;
    }

    public CodeFunction? At(ulong address) => IndexOf(address) is var i and >= 0 ? functions[i] : null;

    /// <summary>address 是否恰为某个函数的入口。</summary>
    public bool IsEntry(ulong address) => Array.BinarySearch(starts, address) >= 0;

    public int EntryIndex(ulong address) => Array.BinarySearch(starts, address) is var i and >= 0 ? i : -1;

    /// <summary>读取 pc 处的指令字；勘误补丁位置返回原指令。pc 不在可执行节内返回 null。</summary>
    public uint? Word(ulong pc) => patches.TryGetValue(pc, out var patch) ? patch.Original : RawWord(pc);

    public uint? RawWord(ulong pc)
    {
        foreach (var (section, bytes) in code)
            if (section.Contains(pc) && pc - section.Address + 4 <= section.Size)
                return BinaryPrimitives.ReadUInt32LittleEndian(bytes.Span[(int)(pc - section.Address)..]);
        return null;
    }

    public CodeRegion RegionOf(ulong address) => Region(Image.SectionAt(address));

    private static CodeRegion Region(ImageSection? section) => section?.Name switch
    {
        "il2cpp" => CodeRegion.Managed,
        ".text" => CodeRegion.Runtime,
        ".plt" => CodeRegion.Plt,
        _ => CodeRegion.Other,
    };

    public static CodeMap Build(ImageDocument image)
    {
        if (image.Architecture != Architecture.Arm64) throw new NotSupportedException("代码地图只支持 ARM64 ELF");
        var code = image.Sections.Where(s => s.Executable).Select(s =>
        {
            var resolved = image.Resolve(s.Address);
            if (resolved.Kind != AddressKind.FileBacked || resolved.AvailableBytes < s.Size)
                throw new InvalidDataException($"可执行节 {s.Name} 未完整映射到文件");
            return (s, image.Bytes.Slice(checked((int)resolved.FileOffset!.Value), checked((int)s.Size)));
        }).ToArray();
        if (code.Length == 0) throw new InvalidDataException("没有可执行节");

        var table = FunctionTable.Build(image);
        var list = new List<CodeFunction>(table.Ranges.Count + 1024);
        foreach (var range in table.Ranges)
            list.Add(new(range.Start, range.End, Region(image.SectionAt(range.Start)), range.Evidence) { ExceptionRegions = range.ExceptionRegions });

        uint Raw(ulong pc)
        {
            foreach (var (section, bytes) in code)
                if (section.Contains(pc)) return BinaryPrimitives.ReadUInt32LittleEndian(bytes.Span[(int)(pc - section.Address)..]);
            throw new InvalidDataException($"0x{pc:x} 不在可执行节内");
        }

        // PLT：PLT0 占 32 字节，其后每项 16 字节：adrp x16, page; ldr x17, [x16, #off]; add x16, x16, #off; br x17
        if (image.Section(".plt") is { } plt)
        {
            for (var stub = plt.Address + 32; stub + 16 <= plt.Address + plt.Size; stub += 16)
            {
                uint w0 = Raw(stub), w1 = Raw(stub + 4), w2 = Raw(stub + 8), w3 = Raw(stub + 12);
                if (!A64.IsAdrp(w0) || A64.Rd(w0) != 16 || (w1 & 0xFFC003FF) != 0xF9400211 || !A64.IsAddImmediate64(w2) || w3 != 0xD61F0220)
                    throw new InvalidDataException($"PLT 项 0x{stub:x} 不是标准桩序列");
                var slot = A64.AdrpPage(w0, stub) + A64.AccessOffset(w1);
                if (A64.AdrpPage(w0, stub) + A64.AddImmediate(w2) != slot) throw new InvalidDataException($"PLT 项 0x{stub:x} 的 ldr/add 偏移不一致");
                var name = image.Imports.GetValueOrDefault(slot) ?? image.SymbolSlots.GetValueOrDefault(slot);
                list.Add(new(stub, stub + 16, CodeRegion.Plt, BoundaryEvidence.PltStub) { Import = name });
            }
        }
        list.Sort((a, b) => a.Start.CompareTo(b.Start));

        // 勘误补丁：空隙中成对出现的 "访存指令; b Site+4"，且 Site 处为 b 到该对。
        var patches = new Dictionary<ulong, ErratumPatch>();
        var gapRanges = Uncovered(code, list);
        foreach (var (start, end) in gapRanges)
            for (var pc = start; pc + 8 <= end; pc += 4)
            {
                uint first = Raw(pc), second = Raw(pc + 4);
                if (!A64.IsB(second)) continue;
                var back = A64.Imm26Target(second, pc + 4);
                var site = back - 4;
                if (!code.Any(c => c.s.Contains(site))) continue;
                var at = Raw(site);
                if (!A64.IsB(at) || A64.Imm26Target(at, site) != pc) continue;
                if (!(A64.IsUnsignedOffsetAccess(first) || (first & 0x3B000000) == 0x38000000 || (first & 0x3A000000) == 0x28000000)) continue;
                // 勘误序列以 ADRP 开头，被替换的访存指令在其后 1–3 条（记录最近 ADRP 的页内偏移供核对）。
                int? adrpOffset = null;
                for (var k = 1; k <= 4 && adrpOffset is null; k++)
                {
                    var adrp = site - 4UL * (ulong)k;
                    if (A64.IsAdrp(Raw(adrp))) adrpOffset = (int)(adrp & 0xFFF);
                }
                patches[site] = new ErratumPatch(site, pc, first, adrpOffset);
                pc += 4;
            }

        // 没有 FDE、但被引用为入口的目标（BL/B 目标、ADRP+ADD/ADR 构造的代码指针、重定位指针）。
        var sortedStarts = list.Select(f => f.Start).ToArray();
        int Owner(ulong a)
        {
            var i = Array.BinarySearch(sortedStarts, a);
            if (i < 0) i = ~i - 1;
            return i >= 0 && list[i].Contains(a) ? i : -1;
        }
        bool Covered(ulong a) => Owner(a) >= 0;
        var stubArea = patches.Values.Select(p => p.Stub).ToHashSet();
        var referenced = new Dictionary<ulong, string>();
        void Candidate(ulong target, string how)
        {
            if (Covered(target) || stubArea.Contains(target) || !code.Any(c => c.s.Contains(target))) return;
            referenced.TryAdd(target, how);
        }
        foreach (var (section, bytes) in code)
        {
            var span = bytes.Span;
            for (var offset = 0; offset + 4 <= span.Length; offset += 4)
            {
                var w = BinaryPrimitives.ReadUInt32LittleEndian(span[offset..]);
                var pc = section.Address + (ulong)offset;
                if (A64.IsBl(w)) Candidate(A64.Imm26Target(w, pc), "bl");
                else if (A64.IsB(w) && !patches.ContainsKey(pc))
                {
                    // 函数内跳转不是入口证据；只有跳出所在函数的 B 才算
                    var target = A64.Imm26Target(w, pc);
                    var owner = Owner(pc);
                    if (owner < 0 || !list[owner].Contains(target)) Candidate(target, "b");
                }
                else if (A64.IsAdr(w)) Candidate(A64.AdrTarget(w, pc), "adr");
                else if (A64.IsAdrp(w) && offset + 8 <= span.Length)
                {
                    var next = BinaryPrimitives.ReadUInt32LittleEndian(span[(offset + 4)..]);
                    if (A64.IsAddImmediate64(next) && A64.Rn(next) == A64.Rd(w))
                        Candidate(A64.AdrpPage(w, pc) + A64.AddImmediate(next), "adrp+add");
                }
            }
        }
        foreach (var target in image.RelocatedPointerTargets()) Candidate(target, "reloc");

        // 终点取下一个已知入口（FDE 或其他被引用入口）、节尾或补丁桩，三者最近者。
        var allStarts = sortedStarts.Concat(referenced.Keys).Order().ToArray();
        foreach (var (entry, _) in referenced.OrderBy(p => p.Key))
        {
            var i = Array.BinarySearch(allStarts, entry);
            var next = i + 1 < allStarts.Length ? allStarts[i + 1] : ulong.MaxValue;
            var section = code.First(c => c.s.Contains(entry)).s;
            var end = Math.Min(next, section.Address + section.Size);
            foreach (var p in patches.Values) if (p.Stub > entry && p.Stub < end) end = p.Stub;
            list.Add(new(entry, end, Region(section), BoundaryEvidence.Reference));
        }
        list.Sort((a, b) => a.Start.CompareTo(b.Start));
        for (var i = 1; i < list.Count; i++)
            if (list[i].Start < list[i - 1].End)
                throw new InvalidDataException($"函数范围重叠：0x{list[i - 1].Start:x}..0x{list[i - 1].End:x} 与 0x{list[i].Start:x}");

        var stubs = patches.Values.SelectMany(p => new[] { p.Stub, p.Stub + 4 }).ToHashSet();
        var gaps = new List<CodeGap>();
        foreach (var (start, end) in Uncovered(code, list))
        {
            var words = new List<uint>();
            for (var pc = start; pc + 4 <= end; pc += 4) words.Add(Raw(pc));
            var kind = Enumerable.Range(0, words.Count).All(k => stubs.Contains(start + 4UL * (ulong)k)) ? "erratum-stubs"
                : words.All(w => w == A64.Nop || A64.IsTrap(w)) ? "padding"
                : Enumerable.Range(0, words.Count).All(k => stubs.Contains(start + 4UL * (ulong)k) || words[k] == A64.Nop || A64.IsTrap(words[k])) ? "erratum-stubs+padding"
                : "unexplained";
            gaps.Add(new(start, end, kind));
        }
        return new(image, code, list.ToArray(), patches, gaps.ToArray(), table.Skipped, referenced);
    }

    private static List<(ulong Start, ulong End)> Uncovered((ImageSection s, ReadOnlyMemory<byte>)[] code, List<CodeFunction> sorted)
    {
        var result = new List<(ulong, ulong)>();
        foreach (var (section, _) in code)
        {
            var cursor = section.Address;
            var end = section.Address + section.Size;
            foreach (var f in sorted)
            {
                if (f.End <= section.Address || f.Start >= end) continue;
                if (f.Start > cursor) result.Add((cursor, f.Start));
                cursor = Math.Max(cursor, f.End);
            }
            if (cursor < end) result.Add((cursor, end));
        }
        return result;
    }
}
