using System.Security.Cryptography;
using System.Text;
using Cpp2CS.Input;
using Cpp2CS.Spec.Runtime;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>ELF 对象范围与 AAELF64 动态重定位。只读对象的内容和每个指针所指的对象分别参与比较。</summary>
internal sealed class FingerprintData
{
    private readonly Elf64 elf;
    private readonly byte[] file;
    private readonly ElfSection[] sections;
    private readonly ElfSegment[] relro;
    private readonly ElfRela[] relocations;
    private readonly Dictionary<ulong, (ulong End, bool Conflict)> sizes = [];
    private (ulong Start, ulong End, ulong MaxEnd, bool Conflict)[]? intervals;

    public FingerprintData(Elf64 elf, byte[] file)
    {
        this.elf = elf;
        this.file = file;
        sections = [.. elf.Sections.Where(s => (s.Flags & 6) == 2 && s.Size > 0)];
        relro = [.. elf.Segments.Where(s => s.Type == 0x6474e552)];
        relocations = [.. elf.Relocations.Where(r => r.Type != 0).OrderBy(r => r.Address)];
        AddBounds(elf.DynamicSymbols.Concat(elf.ObjectSymbols()).Where(s => (s.Info & 15) == 1 &&
            s.Section > 0 && s.Section < elf.Sections.Count).Select(s => (s.Value, s.Size)));
    }

    public void AddBounds(IEnumerable<(ulong Address, ulong Size)> bounds)
    {
        foreach (var (address, size) in bounds)
        {
            if (size == 0 || size > ulong.MaxValue - address) continue;
            if (!sections.Any(s => ((s.Flags & 1) == 0 || s.Name == ".data.rel.ro") &&
                Contains(s.Address, s.Size, address, size))) continue;
            ulong end = address + size;
            if (!sizes.TryAdd(address, (end, false)) && sizes[address].End != end)
                sizes[address] = (Math.Max(end, sizes[address].End), true);
            intervals = null;
        }
    }

    // 前缀最大终点用于找全覆盖该地址的对象；别名范围有分歧时没有确切界限。
    private (ulong Start, ulong End)? ObjectAt(ulong address)
    {
        if (intervals == null)
        {
            ulong maxEnd = 0;
            intervals = [.. sizes.OrderBy(p => p.Key).Select(p =>
                (p.Key, p.Value.End, maxEnd = Math.Max(maxEnd, p.Value.End), p.Value.Conflict))];
        }
        int lo = 0, hi = intervals.Length;
        while (lo < hi)
        {
            int mid = lo + (hi - lo) / 2;
            if (intervals[mid].Start <= address) lo = mid + 1;
            else hi = mid;
        }
        (ulong, ulong)? found = null;
        for (int i = lo - 1; i >= 0 && intervals[i].MaxEnd > address; i--)
        {
            var obj = intervals[i];
            if (obj.End <= address) continue;
            if (obj.Conflict || found.HasValue) return (0, 0);
            found = (obj.Start, obj.End);
        }
        return found;
    }

    private static bool Contains(ulong start, ulong count, ulong address, ulong width) =>
        address >= start && address - start < count && width <= count - (address - start);

    public bool Reference(int offset, ulong address, int width, IReadOnlySet<ulong> entries, List<FingerprintReference> output)
    {
        int first = output.Count;
        if (Describe(offset, address, width, entries, output, null, [])) return true;
        output.RemoveRange(first, output.Count - first);
        return false;
    }

    private bool Describe(int offset, ulong address, int width, IReadOnlySet<ulong> entries, List<FingerprintReference> output,
        string? path, HashSet<ulong> active)
    {
        if (width == 0 && entries.Contains(address))
        {
            output.Add(new(offset, ReferenceKind.Code, address) { Path = path });
            return true;
        }
        var section = Array.Find(sections, s => Contains(s.Address, s.Size, address, (uint)width));
        if (section == null) return false;
        bool protectedData = relro.Any(s => Contains(s.Address, s.MemorySize, address, (uint)width));
        if ((section.Flags & 1) != 0 && !protectedData)
        {
            if (section.Name is ".got" or ".data.rel.ro" || relro.Any(s => Contains(s.Address, s.MemorySize, address, 0))) return false;
            output.Add(new(offset, ReferenceKind.Writable, address) { Path = path });
            return true;
        }
        if (section.Type != 1 || protectedData && section.Name is not (".got" or ".data.rel.ro")) return false;
        int length = width;
        ulong interior = 0;
        if (length == 0 && ObjectAt(address) is { } obj)
        {
            if (obj.End <= obj.Start || !Contains(section.Address, section.Size, obj.Start, obj.End - obj.Start)) return false;
            length = checked((int)(obj.End - obj.Start));
            interior = address - obj.Start;
            address = obj.Start;
        }
        int delta = checked((int)(address - section.Address));
        var bytes = file.AsSpan(checked((int)section.Offset + delta), checked((int)section.Size - delta));
        if (length == 0)
        {
            if ((section.Flags & 0x20) != 0 && section.EntrySize is 1 or 2 or 4 && (ulong)delta % section.EntrySize == 0)
            {
                int unit = (int)section.EntrySize;
                for (int i = 0; i <= bytes.Length - unit; i += unit)
                    if (bytes.Slice(i, unit).IndexOfAnyExcept((byte)0) < 0) { length = i + unit; break; }
                if (length == 0) return false;
            }
            else return false;
        }
        if (protectedData && !relro.Any(s => Contains(s.Address, s.MemorySize, address, (uint)length))) return false;
        // 有环或过深的对象图保留为不可比。
        if (active.Count >= 32 || !active.Add(address)) return false;
        int root = output.Count;
        output.Add(new(offset, ReferenceKind.ReadOnly, interior) { Path = path });
        bytes = bytes[..length];
        byte[]? masked = null;
        int start = FirstAtOrAfter(address);
        if (start > 0 && RelocationOverlaps(relocations[start - 1], address)) return false;
        ulong end = address + (uint)length, previousEnd = address;
        for (int i = start; i < relocations.Length && relocations[i].Address < end; i++)
        {
            var r = relocations[i];
            if ((r.Address & 7) != 0 || r.Address < previousEnd || end - r.Address < 8 ||
                r.Type is not (257 or 1025 or 1026 or 1027)) return false;
            int member = checked((int)(r.Address - address));
            masked ??= bytes.ToArray();
            masked.AsSpan(member, 8).Clear();
            string memberPath = $"{path}/{member:X8}";
            if (!Pointer(r, out ulong? target, out var binding)) return false;
            int memberRow = output.Count;
            if (target.HasValue)
            {
                if (!Describe(offset, target.Value, 0, entries, output, memberPath, active)) return false;
            }
            else output.Add(new(offset, ReferenceKind.Import, 0) { Path = memberPath });
            if (binding != null) output[memberRow] = output[memberRow] with { Binding = binding };
            previousEnd = r.Address + 8;
        }
        if (section.Name == ".got" && (width != 8 || start == relocations.Length || relocations[start].Address != address))
            return false;
        output[root] = output[root] with { Digest = Convert.ToHexString(SHA256.HashData(masked == null ? bytes : masked)) };
        active.Remove(address);
        return true;
    }

    private bool RelocationOverlaps(ElfRela r, ulong address)
    {
        ulong size = r.Type switch
        {
            1024 when r.Symbol < elf.DynamicSymbols.Count => elf.DynamicSymbols[(int)r.Symbol].Size,
            1031 => 16, // TLSDESC
            258 or 261 => 4,
            259 or 262 => 2,
            _ => 8
        };
        return address - r.Address < size;
    }

    private int FirstAtOrAfter(ulong address)
    {
        int lo = 0, hi = relocations.Length;
        while (lo < hi)
        {
            int mid = lo + (hi - lo) / 2;
            if (relocations[mid].Address < address) lo = mid + 1;
            else hi = mid;
        }
        return lo;
    }

    private bool Pointer(ElfRela r, out ulong? target, out FingerprintBinding? binding)
    {
        ulong addend = unchecked((ulong)r.Addend);
        target = addend;
        binding = null;
        if (r.Type == 1027) return r.Symbol == 0;
        if (r.Symbol == 0 || r.Symbol >= elf.DynamicSymbols.Count || r.Type == 1026 && r.Addend != 0) return false;
        var symbol = elf.DynamicSymbols[(int)r.Symbol];
        if ((symbol.Info & 15) is not (0 or 1 or 2) || symbol.Section >= elf.Sections.Count) return false;
        // 可抢占的定义同时核对动态查找身份和本映像内的定义。纯导入只核对前者。
        if (symbol.Section == 0 || (symbol.Info >> 4) != 0 && (symbol.Visibility & 3) == 0 && !elf.BindsLocally)
        {
            if (elf.SymbolIdentity(r.Symbol) is not string identity) return false;
            binding = new(symbol.Name, addend, Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(identity))));
        }
        target = symbol.Section == 0 ? null : unchecked(symbol.Value + addend);
        return true;
    }
}
