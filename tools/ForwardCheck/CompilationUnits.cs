using System.Runtime.InteropServices;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>libdw 按 DW_AT_ranges 或 low_pc/high_pc 解释编译单元的地址范围。</summary>
internal sealed class CompilationUnits
{
    internal enum Owner { Unknown, Runtime, Generated }
    private readonly List<(ulong Start, ulong End, Owner Owner)> spans = [];

    internal CompilationUnits(string path, Action<IEnumerable<(ulong Address, ulong Size)>>? objects = null)
    {
        var events = new SortedDictionary<ulong, (int Runtime, int Generated)>();
        void Add(ulong pc, Owner owner, int count)
        {
            var e = events.GetValueOrDefault(pc);
            events[pc] = owner == Owner.Runtime ? (e.Runtime + count, e.Generated) : (e.Runtime, e.Generated + count);
        }
        Visit(path, die =>
        {
            objects?.Invoke(DwarfObjects.InUnit(die));
            string name = (Marshal.PtrToStringUTF8(dwarf_diename(die)) ?? "").Replace('\\', '/');
            var owner = name.EndsWith(".lump.cpp", StringComparison.OrdinalIgnoreCase) ? LumpOwner(die, name) : Classify(name);
            if (owner == Owner.Unknown || dwarf_hasattr(die, 0x55) == 0 && dwarf_hasattr(die, 0x11) == 0) return;
            nint cursor = 0;
            ulong basis = 0;
            while ((cursor = dwarf_ranges(die, cursor, ref basis, out ulong start, out ulong end)) > 0)
            {
                if (start == 0 || start >= end) continue;
                Add(start, owner, 1);
                Add(end, owner, -1);
            }
            if (cursor < 0) throw new InvalidDataException("无法读取编译单元范围");
        });
        int runtime = 0, generated = 0;
        ulong previous = 0;
        foreach (var (pc, delta) in events)
        {
            if (previous < pc && (runtime > 0 || generated > 0))
                spans.Add((previous, pc, generated > 0 ? Owner.Generated : Owner.Runtime));
            runtime += delta.Runtime;
            generated += delta.Generated;
            previous = pc;
        }
        if (!spans.Any(s => s.Owner == Owner.Runtime)) throw new InvalidDataException("没有运行时编译单元的地址范围");
    }

    internal static void Visit(string path, Action<nint> visit)
    {
        using var stream = File.OpenRead(path);
        var dwarf = dwarf_begin(stream.SafeFileHandle.DangerousGetHandle().ToInt32(), 0);
        if (dwarf == 0) throw new InvalidDataException("无法打开 DWARF");
        var die = Marshal.AllocHGlobal(IntPtr.Size * 4);
        try
        {
            ulong offset = 0;
            int rc;
            while ((rc = dwarf_nextcu(dwarf, offset, out ulong next, out nuint header, 0, 0, 0)) == 0)
            {
                if (dwarf_offdie(dwarf, offset + header, die) == 0) throw new InvalidDataException("无法读取编译单元");
                visit(die);
                offset = next;
            }
            if (rc < 0) throw new InvalidDataException("编译单元头无效");
        }
        finally { Marshal.FreeHGlobal(die); dwarf_end(dwarf); }
    }

    // Bee 的合并单元在调试行表中列出被包含的源文件。成员归属一致才用整个单元的范围。
    private static Owner LumpOwner(nint die, string unit)
    {
        if (dwarf_getsrcfiles(die, out nint files, out nuint count) != 0) return Owner.Unknown;
        Owner? owner = null;
        for (nuint i = 0; i < count; i++)
        {
            string file = (Marshal.PtrToStringUTF8(dwarf_filesrc(files, i, 0, 0)) ?? "").Replace('\\', '/');
            if (Path.GetFileName(file) == Path.GetFileName(unit) ||
                Path.GetExtension(file).ToLowerInvariant() is not (".c" or ".cc" or ".cpp" or ".cxx")) continue;
            var member = Classify(file);
            if (member == Owner.Unknown || owner.HasValue && owner != member) return Owner.Unknown;
            owner = member;
        }
        return owner ?? Owner.Unknown;
    }

    private static Owner Classify(string path)
    {
        string unit = "/" + path;
        if (unit.Contains("/il2cppOutput/", StringComparison.OrdinalIgnoreCase)) return Owner.Generated;
        if (unit.Contains("/il2cpp/libil2cpp/", StringComparison.OrdinalIgnoreCase) ||
            unit.Contains("/il2cpp/external/", StringComparison.OrdinalIgnoreCase) ||
            unit.Contains("/artifacts/baselib/", StringComparison.OrdinalIgnoreCase) ||
            unit.Contains("/llvm-project/libcxx/src/", StringComparison.Ordinal) ||
            unit.Contains("/llvm-project/libcxxabi/src/", StringComparison.Ordinal) ||
            unit.Contains("/llvm-project/libunwind/src/", StringComparison.Ordinal)) return Owner.Runtime;
        return Owner.Unknown;
    }

    internal Owner At(ulong address)
    {
        int lo = 0, hi = spans.Count;
        while (lo < hi)
        {
            int mid = lo + (hi - lo) / 2;
            var span = spans[mid];
            if (address < span.Start) hi = mid;
            else if (address >= span.End) lo = mid + 1;
            else return span.Owner;
        }
        return Owner.Unknown;
    }

    private const string Library = "libdw.so.1";
    [DllImport(Library)] private static extern nint dwarf_begin(int fd, int command);
    [DllImport(Library)] private static extern int dwarf_end(nint dwarf);
    [DllImport(Library)] private static extern int dwarf_nextcu(nint dwarf, ulong offset, out ulong next, out nuint header,
        nint abbrev, nint addressSize, nint offsetSize);
    [DllImport(Library)] private static extern nint dwarf_offdie(nint dwarf, ulong offset, nint result);
    [DllImport(Library)] private static extern nint dwarf_diename(nint die);
    [DllImport(Library)] private static extern int dwarf_getsrcfiles(nint die, out nint files, out nuint count);
    [DllImport(Library)] private static extern nint dwarf_filesrc(nint files, nuint index, nint mtime, nint length);
    [DllImport(Library)] private static extern int dwarf_hasattr(nint die, uint attribute);
    [DllImport(Library)] private static extern nint dwarf_ranges(nint die, nint offset, ref ulong basis, out ulong start, out ulong end);
}
