using System.Buffers.Binary;
using Cpp2CS.Input;
using Cpp2CS.Target;

namespace Cpp2CS.Tools.LiftCheck;

internal sealed class Image
{
    readonly byte[] file;
    readonly ElfSegment[] loads;
    readonly bool disjoint;
    public Image(Elf64 elf, byte[] bytes)
    {
        file = (byte[])bytes.Clone();
        loads = elf.Segments.Where(s => s.Type == 1).ToArray();
        disjoint = loads.All(a => loads.All(b => a == b || a.Address >= b.Address + b.MemorySize || b.Address >= a.Address + a.MemorySize));
        ulong imports = (loads.Max(s => s.Address + s.MemorySize) + 65535) & ~65535ul;
        var addresses = elf.DynamicSymbols.Where(s => s.Section == 0).Select(s => s.Name).Distinct(StringComparer.Ordinal)
            .Select((name, j) => (name, value: imports + 16ul * (uint)(j + 1))).ToDictionary(p => p.name, p => p.value);
        foreach (var r in elf.Relocations)
        {
            if (r.Type == 0) continue;
            ulong value;
            if (r.Type == 1027 && r.Symbol == 0) value = (ulong)r.Addend;
            else if (r.Type is 257 or 1025 or 1026)
            {
                var s = elf.DynamicSymbols[(int)r.Symbol];
                value = (s.Section == 0 ? addresses[s.Name] : s.Value) + (ulong)r.Addend;
            }
            else throw new InvalidDataException($"未处理的重定位 {r.Type}");
            if (elf.FileOffset(r.Address, 8) is int offset)
                BinaryPrimitives.WriteUInt64LittleEndian(file.AsSpan(offset), value);
            else
                for (int j = 0; j < 8; j++) zeroFill[r.Address + (uint)j] = (byte)(value >> (8 * j));
        }
    }
    readonly Dictionary<ulong, byte> zeroFill = [];
    public byte Byte(ulong address, ulong seed)
    {
        foreach (var s in loads)
        {
            ulong delta = address - s.Address;
            if (delta < s.MemorySize) return delta < s.FileSize ? file[(int)(s.Offset + delta)] : zeroFill.GetValueOrDefault(address);
        }
        return (byte)(EnvironmentState.MemoryWord(seed, address & ~7ul) >> (8 * (int)(address & 7)));
    }

    public void Page(ulong page, Span<byte> bytes, ulong seed)
    {
        if (disjoint)
        {
            foreach (var s in loads)
            {
                ulong delta = page - s.Address;
                if (delta >= s.FileSize || (uint)bytes.Length > s.FileSize - delta) continue;
                file.AsSpan((int)(s.Offset + delta), bytes.Length).CopyTo(bytes);
                return;
            }
        }
        for (int i = 0; i < bytes.Length; i += 8)
            BinaryPrimitives.WriteUInt64LittleEndian(bytes[i..], EnvironmentState.MemoryWord(seed, page + (uint)i));
        foreach (var s in loads)
        {
            ulong start = Math.Max(page, s.Address), end = Math.Min(page + (uint)bytes.Length, s.Address + s.MemorySize);
            if (start >= end) continue;
            var dest = bytes.Slice((int)(start - page), (int)(end - start));
            dest.Clear();
            if (start < s.Address + s.FileSize)
            {
                int n = (int)(Math.Min(end, s.Address + s.FileSize) - start);
                file.AsSpan((int)(s.Offset + start - s.Address), n).CopyTo(dest);
            }
            if (zeroFill.Count != 0 && end > s.Address + s.FileSize)
                for (ulong p = Math.Max(start, s.Address + s.FileSize); p < end; p++) bytes[(int)(p - page)] = zeroFill.GetValueOrDefault(p);
        }
    }
}

internal static class EnvironmentState
{
    public const int StepLimit = 4096;
    public static readonly ulong[] Seeds = [11, 29, 47, 61, 83];
    public static readonly ulong[] TableSeeds = [.. Seeds, 101, 103, 107];
    static bool TableBias(ulong seed) => seed is 101 or 103 or 107;
    public static ulong Mix(ulong x)
    {
        x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;
        x = (x ^ (x >> 27)) * 0x94d049bb133111eb;
        return x ^ (x >> 31);
    }
    public static bool Biased(ulong seed) => seed is 61 or 83 || TableBias(seed);
    public static ulong MemoryWord(ulong seed, ulong address)
    {
        ulong sample = Mix(address + 0x9e3779b97f4a7c15ul * seed);
        if (TableBias(seed) && (sample & 3) != 0)
        {
            // 两个相邻的 32 位槽均取小整数，窄字段保持同一内存的小端字节关系。
            ulong low = (sample >> 8) & 15, high = (sample >> 16) & 15;
            return low | high << 32;
        }
        if (Biased(seed))
        {
            // 以八字节为单位生成环境；同一位置的不同宽度访问保持小端重叠关系。
            switch (sample & 7)
            {
                case 0: case 1: return 0;
                case 2: return 1;
                case 3: return (sample >> 8) & 7;
            }
        }
        return (sample & 0x00000000fffffff8ul) + 0x200000000ul;
    }
    public static UInt128 Register(ulong seed, int r, int call = 0)
    {
        ulong key = seed * 0x9e3779b97f4a7c15ul + (uint)r + (ulong)(uint)call * 256;
        if (call == 0 && r is 30 or 31 or Abi.Thread)
            return r switch { 30 => 0x6fff00000000ul, 31 => 0x5001000000ul, _ => 0x6001000000ul };
        if (r is >= 32 and < 64)
        {
            ulong low = Mix(~key), high = Mix(key);
            if (Biased(seed))
            {
                // 同时给单、双精度运算提供带负载的两类 NaN 及有符号零。
                low = (high & 7) switch
                {
                    0 => 0x7ff000017f800001ul, 1 => 0xfff80001ffc00001ul,
                    2 => 0x8000000080000000ul, 3 => 0, _ => low
                };
            }
            return ((UInt128)high << 64) | low;
        }
        if (call == 0 && r < 8 && seed == 11) return (uint)r;
        if (TableBias(seed) && r < 8 && (Mix(key) & 3) != 0) return (Mix(key) >> 8) & 15;
        if (Biased(seed) && r < 8)
        {
            ulong sample = Mix(key);
            switch (sample & 15)
            {
                case 0: case 1: case 2: return 0;
                case 3: return 1;
                case 4: return ulong.MaxValue;
                case 5: return 1ul << 63;
                case 6: return long.MaxValue;
                case 7: return 0x80000000;
                case 8: return int.MaxValue;
            }
        }
        return MemoryWord(seed, key);
    }
}

internal readonly record struct TraceEvent(string Kind, ulong Address, int Width, UInt128 Value, int Slot = 0, UInt128 Undefined = default, ulong Pc = 0)
{
    public bool Matches(TraceEvent native) =>
        Kind == native.Kind && Address == native.Address && Width == native.Width && Slot == native.Slot &&
        ((Value ^ native.Value) & ~Undefined) == 0;
}
internal sealed class Trace
{
    public List<TraceEvent> Events { get; } = [];
    public ulong Pc;
    public int Instructions;
    public bool Exhausted;
    public string? Error;
    public string? Diagnostic;
    public void Row(string kind, int width, Bits value, int slot) =>
        Events.Add(new(kind, 0, width, value.Value, slot, value.Undefined, Pc));
    public void Add(string kind, ulong address = 0, int width = 0, UInt128 value = default, int slot = 0) =>
        Events.Add(new(kind, address, width, value, slot, Pc: Pc));
}
