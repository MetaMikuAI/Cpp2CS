namespace Cpp2CS.Input;

/// <summary>il2cpp-class-internals.h、il2cpp-pinvoke-support.h 的 LP64 代码指针。地址均为链接地址。</summary>
public sealed class RegisteredEntries
{
    public HashSet<ulong> Managed { get; } = [];
    public HashSet<ulong> Runtime { get; } = [];

    public RegisteredEntries(Il2CppInput input)
    {
        var elf = input.Elf;
        ulong code = checked(input.Code.CodeRegistration + elf.ImageBase);
        void Add(HashSet<ulong> set, ulong address)
        {
            if (address == 0) return;
            if (!elf.IsExecutable(address)) throw new InvalidDataException("登记的函数入口不在代码段");
            set.Add(address);
        }
        void Table(HashSet<ulong> set, ulong owner, int countAt, int pointerAt, int stride, params int[] fields)
        {
            ulong table = elf.Pointer(owner + (uint)pointerAt);
            if (table == 0) return;
            uint count = elf.Word(owner + (uint)countAt);
            if (count != 0 && !elf.Mapped(table, (ulong)count * (uint)stride)) throw new InvalidDataException("登记表越界");
            for (uint i = 0; i < count; i++)
                foreach (int field in fields) Add(set, elf.Pointer(table + (ulong)i * (uint)stride + (uint)field));
        }
        foreach (var m in input.Code.Methods.Concat(input.Code.MethodInstances))
            if (m.Entry is ulong rva) Add(Managed, checked(elf.ImageBase + rva));
        Table(Managed, code, 16, 24, 8, 0);
        // MetadataCache::MakeGenericMethodPointers 用独立的 adjustorThunkIndex 取托管方法的虚调用入口。
        ulong metadata = checked(input.Code.MetadataRegistration + elf.ImageBase);
        ulong functions = elf.Pointer(metadata + 40), adjustors = elf.Pointer(code + 32);
        uint methods = elf.Word(metadata + 32);
        for (uint i = 0; i < methods; i++)
        {
            int index = unchecked((int)elf.Word(functions + 16ul * i + 12));
            if (index == -1) continue;
            if (index < 0 || adjustors == 0) throw new InvalidDataException("泛型调整入口下标无效");
            Add(Managed, elf.Pointer(adjustors + 8ul * (uint)index));
        }
        Table(Runtime, code, 0, 8, 8, 0);
        Table(Runtime, code, 40, 48, 8, 0);
        foreach (int slot in new[] { 64, 72, 80 }) Table(Runtime, code, 56, slot, 8, 0);
        Table(Runtime, code, 88, 96, 56, 0, 8, 16, 24, 32);
        Table(Runtime, code, 104, 112, 16, 8);
        foreach (ulong module in Registrations.Pointers(elf, elf.Pointer(code + 128), checked((int)elf.Word(code + 120))))
        {
            Table(Managed, module, 8, 16, 8, 0);
            Table(Managed, module, 24, 32, 16, 8);
            Add(Runtime, elf.Pointer(module + 104));
        }
        Runtime.ExceptWith(Managed);
    }
}
