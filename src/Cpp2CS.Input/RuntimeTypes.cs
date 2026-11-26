using System.Reflection;
using Cpp2CS.Model;
using static Cpp2CS.Input.MetadataFile;

namespace Cpp2CS.Input;

internal sealed class RuntimeTypes(Elf64 elf, MetadataFile metadata, ulong[] typePointers)
{
    private readonly Dictionary<ulong, TypeReference> types = new();
    private readonly Dictionary<ulong, TypeReference[]> arguments = new();
    private readonly HashSet<ulong> active = [];
    internal ushort Flags(int index) => (ushort)elf.Word(typePointers[index] + 8);
    internal TypeReference At(int index) => Read(typePointers[index]);

    internal TypeReference[] Arguments(ulong p)
    {
        if (p == 0) throw new InvalidDataException("泛型实参向量为空指针");
        if (arguments.TryGetValue(p, out var cached)) return cached;
        var pointers = Registrations.Pointers(elf, elf.Pointer(p + 8), checked((int)elf.Word(p)));
        var values = Array.ConvertAll(pointers, Read);
        arguments.Add(p, values);
        return values;
    }

    internal NamedType GenericClass(ulong p)
    {
        if (p == 0 || Read(elf.Pointer(p)) is not NamedType { Arguments.Count: 0 } definition)
            throw new InvalidDataException($"泛型类型定义指针无效 0x{p:x}");
        return new(definition.Definition, Arguments(elf.Pointer(p + 8)));
    }

    // il2cpp-runtime-metadata.h 的 Il2CppType.data 随 type 标签取不同的联合成员。
    private TypeReference Read(ulong p)
    {
        if (types.TryGetValue(p, out var cached)) return cached;
        if (p == 0 || !active.Add(p)) throw new InvalidDataException($"空指针或循环的类型描述 0x{p:x}");
        uint bits = elf.Word(p + 8);
        if (((bits >> 24) & 31) != 0 || (bits & (1u << 30)) != 0)
            throw new NotSupportedException($"类型描述 0x{p:x} 含修饰符或 pinned 位");
        int code = (byte)(bits >> 16);
        TypeReference value = code switch
        {
            >= 1 and <= 14 or 0x11 or 0x12 or 0x16 or 0x18 or 0x19 or 0x1c => Definition(p),
            0x0f => new PointerType(Read(elf.Pointer(p))),
            0x1d => new ArrayType(Read(elf.Pointer(p)), 1, true),
            0x14 => ArrayDescription(elf.Pointer(p)),
            0x15 => GenericClass(elf.Pointer(p)),
            0x13 or 0x1e => Variable(checked((int)elf.Word(p)), code == 0x1e),
            _ => throw new NotSupportedException($"类型描述 0x{p:x} 的标签 0x{code:x} 未支持")
        };
        if ((bits & (1u << 29)) != 0) value = new ReferenceType(value);
        active.Remove(p);
        types.Add(p, value);
        return value;
    }

    private NamedType Definition(ulong p)
    {
        int index = checked((int)elf.Word(p));
        metadata.Row(Table.Type, index);
        return new(index, []);
    }
    private VariableType Variable(int index, bool method)
    {
        var row = metadata.Row(Table.GenericParameter, index);
        var owner = metadata.Row(Table.Container, Int(row));
        if ((Int(owner, 8) != 0) != method) throw new InvalidDataException($"泛型参数 {index} 的所有者种类不匹配");
        return new(index, method, Int(owner), Elf64.U16(row, 12));
    }
    private ArrayType ArrayDescription(ulong description)
    {
        int rank = elf.Byte(description + 8);
        if (rank == 0) throw new InvalidDataException("数组秩为零");
        if (elf.Byte(description + 9) != 0 || elf.Byte(description + 10) != 0)
            throw new NotSupportedException("数组签名含显式大小或下界");
        return new(Read(elf.Pointer(description)), rank, false);
    }

    internal GenericParameter[] Parameters(int container, bool method, int ownerIndex)
    {
        if (container == -1) return [];
        var c = metadata.Row(Table.Container, container);
        if (Int(c) != ownerIndex || (Int(c, 8) != 0) != method)
            throw new InvalidDataException($"泛型容器 {container} 的所有者不匹配");
        int start = Int(c, 12), n = Int(c, 4);
        metadata.Range(Table.GenericParameter, start, n);
        var parameters = new GenericParameter[n];
        for (int i = 0; i < n; i++)
        {
            var p = metadata.Row(Table.GenericParameter, start + i);
            if (Int(p) != container || Elf64.U16(p, 12) != i)
                throw new InvalidDataException($"泛型容器 {container} 的参数 {i} 身份不匹配");
            int first = (short)Elf64.U16(p, 8), count = (short)Elf64.U16(p, 10);
            metadata.Range(Table.Constraint, first, count);
            parameters[i] = new(metadata.Name(Int(p, 4)), i, (GenericParameterAttributes)Elf64.U16(p, 14),
                Enumerable.Range(0, count).Select(k => At(Int(metadata.Row(Table.Constraint, first + k)))).ToArray());
        }
        return parameters;
    }
}
