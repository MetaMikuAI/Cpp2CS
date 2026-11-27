using System.Text;
using System.Text.Unicode;
using Cpp2CS.Input;

namespace Cpp2CS.Tools.ForwardCheck;

/// <summary>Itanium C++ ABI 2.9.5：type_info 的第二个指针指向类型名，_ZTI 符号编码同一个类型。</summary>
internal sealed class TypeInfoNames(Elf64 elf, byte[] file, Elf64? symbols)
{
    private readonly ILookup<ulong, string> names = elf.DynamicSymbols.Concat(elf.ObjectSymbols())
        .Concat(symbols?.ObjectSymbols() ?? []).Where(s => s.Section != 0 && (s.Info & 15) == 1 &&
            s.Name.StartsWith("_ZTI", StringComparison.Ordinal)).ToLookup(s => s.Value, s => s.Name[4..]);

    public bool HasSymbol(ulong address) => names.Contains(address);

    public string? Read(ulong address)
    {
        if (address == 0 || elf.FileOffset(address, 16) == null) return null;
        ulong pointer = elf.Pointer(address + 8);
        if (pointer == 0 || elf.FileOffset(pointer) is not int start) return null;
        int end = Array.IndexOf(file, (byte)0, start);
        if (end <= start || elf.FileOffset(pointer, (ulong)(end - start + 1)) == null ||
            !Utf8.IsValid(file.AsSpan(start, end - start)))
            throw new InvalidDataException($"类型信息 0x{address:x} 的名字串无效");
        string name = Encoding.UTF8.GetString(file, start, end - start);
        foreach (string symbol in names[address])
            if (symbol != name) throw new InvalidDataException($"类型信息 0x{address:x} 的名字串 {name} 与符号 _ZTI{symbol} 不一致");
        return name;
    }
}
