using System.Runtime.InteropServices;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>DW_TAG_variable 的固定 DW_OP_addr 位置及 DW_AT_byte_size 或类型大小。</summary>
internal static class DwarfObjects
{
    [StructLayout(LayoutKind.Sequential, Size = 32)]
    private struct Die { }
    [StructLayout(LayoutKind.Sequential, Size = 24)]
    private struct Attribute { }

    public static IEnumerable<(ulong Address, ulong Size)> InUnit(nint root)
    {
        var pending = new Stack<Die>();
        var unit = Marshal.PtrToStructure<Die>(root);
        void Push(int result, Die node)
        {
            if (result < 0) throw new InvalidDataException("DWARF 对象树无效");
            if (result == 0) pending.Push(node);
        }
        Push(dwarf_child(in unit, out var first), first);
        while (pending.TryPop(out var die))
        {
            Push(dwarf_siblingof(in die, out var sibling), sibling);
            Push(dwarf_child(in die, out var child), child);
            if (dwarf_tag(in die) != 0x34 || dwarf_attr(in die, 0x02, out var location) == 0 ||
                dwarf_getlocation(in location, out var ops, out var count) != 0 || count != 1 ||
                Marshal.ReadByte(ops) != 0x03) continue;
            ulong address = unchecked((ulong)Marshal.ReadInt64(ops, 8));
            if (address == 0) continue;
            if (dwarf_attr_integrate(in die, 0x0b, out var bytes) != 0 && dwarf_formudata(in bytes, out ulong size) == 0 ||
                dwarf_attr_integrate(in die, 0x49, out var type) != 0 && dwarf_formref_die(in type, out var target) != 0 &&
                dwarf_aggregate_size(in target, out size) == 0)
                yield return (address, size);
        }
    }

    private const string Library = "libdw.so.1";
    [DllImport(Library)] private static extern int dwarf_child(in Die parent, out Die child);
    [DllImport(Library)] private static extern int dwarf_siblingof(in Die die, out Die sibling);
    [DllImport(Library)] private static extern int dwarf_tag(in Die die);
    [DllImport(Library)] private static extern nint dwarf_attr(in Die die, uint code, out Attribute attribute);
    [DllImport(Library)] private static extern nint dwarf_attr_integrate(in Die die, uint code, out Attribute attribute);
    [DllImport(Library)] private static extern int dwarf_getlocation(in Attribute attribute, out nint operations, out nuint count);
    [DllImport(Library)] private static extern nint dwarf_formref_die(in Attribute attribute, out Die type);
    [DllImport(Library)] private static extern int dwarf_aggregate_size(in Die type, out ulong size);
    [DllImport(Library)] private static extern int dwarf_formudata(in Attribute attribute, out ulong value);
}
