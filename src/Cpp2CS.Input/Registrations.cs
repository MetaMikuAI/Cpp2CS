using Cpp2CS.Model;
using System.Text;

namespace Cpp2CS.Input;

// il2cpp-class-internals.h 中两个注册结构及 CodeGenModule 的 LP64 布局。
internal sealed record Module(ulong Address, int PointerCount);
internal sealed record Registrations(ulong Code, ulong Metadata, Module[] Modules)
{
    internal static Registrations Locate(Elf64 elf, MetadataFile metadata, ImageDefinition[] images)
    {
        var codes = new Dictionary<ulong, Module[]>();
        var metas = new HashSet<ulong>();
        var names = images.Select(i => Encoding.UTF8.GetBytes(i.Name + "\0")).ToArray();
        var methodCounts = images.Select(image => Enumerable.Range(image.FirstType, image.TypeCount)
            .Sum(i => (int)Elf64.U16(metadata.Row(Table.Type, i), 64))).ToArray();
        int typeCount = metadata.Count(Table.Type);
        foreach (var seg in elf.Segments.Where(s => s.Type == 1 && (s.Flags & 1) == 0))
        {
            var content = elf.Slice(seg.Offset, seg.FileSize);
            int alignment = (int)((8 - seg.Address % 8) % 8);
            for (int i = alignment; i <= content.Length - 4; i += 8)
            {
                uint count = Elf64.U32(content, i);
                ulong at = seg.Address + (ulong)i;
                if (count == typeCount && i >= 80 && i + 20 <= content.Length &&
                    Elf64.U32(content, i + 16) == count && ValidMetadata(elf, at - 80))
                    metas.Add(at - 80);
                if (count == images.Length && i >= 120 && elf.TryPointer(at + 8, out var table) &&
                    table != 0 && elf.Mapped(table, (ulong)images.Length * 8) &&
                    ModulesAt(elf, table, names, methodCounts) is { } modules)
                    codes.TryAdd(at - 120, modules);
            }
        }
        if (codes.Count != 1 || metas.Count != 1)
            throw new InvalidDataException($"注册表需要唯一解，代码候选 {codes.Count}，元数据候选 {metas.Count}");
        var code = codes.Single();
        return new(code.Key, metas.Single(), code.Value);
    }

    private static bool ValidMetadata(Elf64 elf, ulong start)
    {
        if (!elf.Mapped(start, 128) || elf.Word(start + 48) == 0) return false;
        // genericClasses、genericInsts、genericMethodTable、types、methodSpecs、fieldOffsets、typeDefinitionsSizes
        ReadOnlySpan<int> strides = [8, 8, 16, 8, 12, 8, 8];
        for (int i = 0; i < strides.Length; i++)
        {
            ulong slot = start + (ulong)i * 16;
            uint n = elf.Word(slot);
            if (n > int.MaxValue || !elf.TryPointer(slot + 8, out var p) ||
                (n != 0 && (p == 0 || !elf.Mapped(p, (ulong)n * (uint)strides[i])))) return false;
        }
        return true;
    }

    private static Module[]? ModulesAt(Elf64 elf, ulong table, byte[][] names, int[] methodCounts)
    {
        var result = new Module[names.Length];
        for (int i = 0; i < names.Length; i++)
        {
            if (!elf.TryPointer(table + (ulong)i * 8, out var module) || module == 0 || !elf.Mapped(module, 136) ||
                !elf.TryPointer(module, out var name) || name == 0) return null;
            int image = Array.FindIndex(names, n => elf.MatchString(name, n));
            if (image < 0 || result[image] != null || elf.Word(module + 8) != methodCounts[image]) return null;
            result[image] = new(module, methodCounts[image]);
        }
        return result;
    }

    internal static ulong[] Pointers(Elf64 elf, ulong address, int count)
    {
        if (count < 0 || count != 0 && (address == 0 || !elf.Mapped(address, (ulong)count * 8)))
            throw new InvalidDataException($"指针表范围无效 0x{address:x}，数量 {count}");
        var result = new ulong[count];
        for (int i = 0; i < count; i++) result[i] = elf.Pointer(address + (ulong)i * 8);
        return result;
    }
    internal ulong[] Vector(Elf64 elf, ulong countSlot) => Pointers(elf, elf.Pointer(countSlot + 8), checked((int)elf.Word(countSlot)));

    internal CodeMap ReadCode(Elf64 elf, MetadataModel model)
    {
        ulong? Entry(ulong address)
        {
            if (address == 0) return null;
            if (!elf.IsExecutable(address)) throw new InvalidDataException($"方法入口位于不可执行区 0x{address:x}");
            return address - elf.ImageBase;
        }
        var invokers = Vector(elf, Code + 40).Select(Entry).ToArray();
        int? Invoker(uint n) => n == uint.MaxValue ? null : n < invokers.Length ? (int)n :
            throw new InvalidDataException($"调用器序号越界 {n}");
        var methods = new MethodCode[model.Methods.Count];
        for (int i = 0; i < Modules.Length; i++)
        {
            var image = model.Images[i];
            var module = Modules[i];
            var pointers = Pointers(elf, elf.Pointer(module.Address + 16), module.PointerCount);
            var indices = elf.Pointer(module.Address + 40);
            var seen = new bool[pointers.Length];
            for (int t = 0; t < image.TypeCount; t++)
            {
                var type = model.Types[image.FirstType + t];
                for (int j = 0; j < type.MethodCount; j++)
                {
                    int m = type.FirstMethod + j;
                    uint token = model.Methods[m].Token;
                    int k = (int)(token & 0xffffff) - 1;
                    if (token >> 24 != 6 || (uint)k >= pointers.Length || seen[k])
                        throw new InvalidDataException($"模块方法令牌无效 0x{token:x8}");
                    seen[k] = true;
                    methods[m] = new(Entry(pointers[k]), indices == 0 ? null : Invoker(elf.Word(indices + (ulong)k * 4)));
                }
            }
        }
        var instances = new MethodCode[model.MethodInstances.Count];
        var assigned = new bool[instances.Length];
        var generic = Vector(elf, Code + 16);
        var functions = elf.Pointer(Metadata + 40);
        uint count = elf.Word(Metadata + 32);
        for (uint i = 0; i < count; i++)
        {
            ulong row = functions + 16ul * i;
            uint spec = elf.Word(row), body = elf.Word(row + 4);
            if (spec >= instances.Length || assigned[spec] || body >= generic.Length)
                throw new InvalidDataException($"泛型方法映射无效，行 {i}，实例 {spec}，入口槽 {body}");
            assigned[spec] = true;
            instances[spec] = new(Entry(generic[body]), Invoker(elf.Word(row + 8)));
        }
        return new(Code - elf.ImageBase, Metadata - elf.ImageBase, methods, instances, invokers);
    }
}
