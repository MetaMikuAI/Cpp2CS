using static Cpp2CS.Targets.Elf.ElfConstants;

namespace Cpp2CS.Targets.Elf;

internal sealed class RelocationCollector(ImageReader reader, List<ImageRange> ranges, ushort machine)
{
    public List<RawRelocation> Relocations { get; } = [];
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
                        Record(address, 8, "RELR", position, kinds);
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
                                Record(checked(next + (ulong)(bit - 1) * 8), 8, "RELR", position, kinds);
                                fixups++;
                            }
                        next = checked(next + 63 * 8);
                    }
                    continue;
                }
                var info = reader.U64(position + 8);
                var kind = (uint)info;
                var size = machine switch
                {
                    AArch64 => ElfWidth(kind),
                    X86_64 => X64Width(kind),
                    _ => throw new NotSupportedException($"ELF machine {machine} 未支持")
                };
                if (size == 0) { Increment(kinds, $"{machine}_NONE"); continue; }
                Record(address, size, $"{machine}_{kind}", position, kinds);
                // REL 的加数读取槽内容；RELA 的加数来自记录。
                if (table.Format is "RELA" or "REL")
                {
                    var addend = table.Format == "RELA" ? reader.I64(position + 16) : unchecked((long)Stored(address));
                    if (kind == (machine == AArch64 ? ArmRelative : X64Relative)) Pointers[address] = (ulong)addend;
                    else if (machine == AArch64 ? kind is ArmAbs64 or ArmGlobDat or ArmJumpSlot : kind is X64Abs64 or X64GlobDat or X64JumpSlot) SymbolPointers[address] = ((uint)(info >> 32), addend);
                }
                fixups++;
            }
            Summaries.Add(new(table.Name, table.Format, table.Offset, table.Size, checked((long)(table.Size / table.Stride)), fixups, kinds));
        }
    }

    private void Record(ulong address, int size, string kind, long position, Dictionary<string, long> kinds)
    {
        var end = checked(address + (ulong)size);
        if (!ranges.Any(r => address >= r.Address && address - r.Address < r.MemorySize && (ulong)size <= r.MemorySize - (address - r.Address)))
            throw new InvalidDataException($"重定位目标不在完整映像范围内：0x{address:X}+{size}");
        Increment(kinds, kind);
        var numeric = kind == "RELR" ? (machine == AArch64 ? ArmRelative : X64Relative) : uint.Parse(kind[(kind.IndexOf('_') + 1)..], System.Globalization.CultureInfo.InvariantCulture);
        Relocations.Add(new(address, size, numeric));
        if (kind == "RELR") Pointers[address] = Stored(address);
        if (executable.Any(r => address < checked(r.Address + r.MemorySize) && end > r.Address))
            CodeRelocations.Add(new(address, size, kind, position));
    }

    private ulong Stored(ulong address)
    {
        var r = ranges.Single(r => address >= r.Address && address - r.Address < r.MemorySize);
        var delta = address - r.Address;
        if (delta >= r.FileSize) return 0;
        if (r.FileSize - delta < 8) throw new InvalidDataException("重定位加数跨越文件边界");
        return reader.U64(r.FileOffset + (long)delta);
    }
    private static int X64Width(uint kind) => kind switch
    {
        X64None => 0,
        X64Abs64 or X64GlobDat or X64JumpSlot or X64Relative or X64Dtpmod64 or X64Dtpoff64 or X64Tpoff64 or X64Irelative => 8,
        X64Pc32 or X64Abs32 or X64Abs32S => 4,
        X64Tlsdesc => 16,
        _ => throw new NotSupportedException($"x86_64 relocation {kind} 未支持")
    };
    private static int ElfWidth(uint kind) => kind switch
    {
        ArmNone => 0,
        ArmAbs64 or ArmPrel64 or ArmGotrel64 or ArmGlobDat or ArmJumpSlot or ArmRelative or ArmTlsDtpmod or ArmTlsDtprel or ArmTlsTprel or ArmIrelative => 8,
        ArmAbs32 or ArmPrel32 or ArmGotrel32 => 4,
        ArmAbs16 or ArmPrel16 => 2,
        >= ArmMovwUabsG0 and <= ArmCondbr19 or >= ArmJump26 and <= ArmMovwPrelG3 or >= ArmMovwGotoffG0 and <= ArmMovwGotoffG3 or >= ArmGotLdPrel19 and <= ArmLd64GotLo12Nc => 4,
        >= ArmTlsgdAdrPrel21 and <= ArmTlsleLdst64TprelLo12Nc => 4,
        ArmTlsdesc => 16,
        _ => throw new NotSupportedException($"AArch64 relocation type {kind} 未支持，不能确认代码覆盖")
    };

    private static void Increment(Dictionary<string, long> counts, string kind) => counts[kind] = counts.GetValueOrDefault(kind) + 1;
}

internal readonly record struct RawRelocation(ulong Address, int Width, uint Kind);
