using Cpp2CS.Model;

namespace Cpp2CS.Input;

/// <summary>MetadataCache::GetRGCTXs 对应的模块内令牌范围，以及 GlobalMetadata 对定义数据的解引用。</summary>
internal static class GenericContexts
{
    internal static Dictionary<RgctxOwner, RgctxDefinition[]> Read(Elf64 elf, Module[] modules, MetadataModel model)
    {
        var contexts = new Dictionary<RgctxOwner, RgctxDefinition[]>();
        for (int i = 0; i < modules.Length; i++)
        {
            ulong module = modules[i].Address;
            var (rangeCount, ranges) = Table(module + 64, 12);
            var (entryCount, entries) = Table(module + 80, 16);
            if (rangeCount == 0) continue;
            var owners = new Dictionary<uint, RgctxOwner>();
            var image = model.Images[i];
            for (int t = image.FirstType; t < image.FirstType + image.TypeCount; t++)
            {
                var type = model.Types[t];
                owners.Add(type.Token, new(false, t));
                for (int m = type.FirstMethod; m < type.FirstMethod + type.MethodCount; m++)
                    owners.Add(model.Methods[m].Token, new(true, m));
            }
            for (int j = 0; j < rangeCount; j++)
            {
                ulong at = ranges + (uint)j * 12ul;
                uint token = elf.Word(at), first = elf.Word(at + 4), length = elf.Word(at + 8);
                if (!owners.TryGetValue(token, out var owner) || (ulong)first + length > (uint)entryCount)
                    throw new InvalidDataException($"上下文定义范围无效，模块 {i}，令牌 0x{token:x8}");
                var rows = new RgctxDefinition[length];
                for (int k = 0; k < rows.Length; k++)
                    rows[k] = Definition(elf, entries + (first + (ulong)k) * 16, model);
                if (!contexts.TryAdd(owner, rows)) throw new InvalidDataException($"上下文定义的所属令牌重复 0x{token:x8}");
            }
        }
        return contexts;

        (int Count, ulong Address) Table(ulong slot, uint stride)
        {
            int count = checked((int)elf.Word(slot));
            ulong address = elf.Pointer(slot + 8);
            if (count != 0 && (address == 0 || !elf.Mapped(address, (ulong)count * stride)))
                throw new InvalidDataException("上下文登记表越界");
            return (count, address);
        }
    }

    private static RgctxDefinition Definition(Elf64 elf, ulong row, MetadataModel model)
    {
        var kind = (RgctxDataType)elf.Word(row);
        if (kind == RgctxDataType.Invalid) return new(kind, null, null);
        ulong data = elf.Pointer(row + 8);
        if (data == 0 || !elf.Mapped(data, kind == RgctxDataType.Constrained ? 8ul : 4ul))
            throw new InvalidDataException("上下文定义数据指针无效");
        uint index = elf.Word(data);
        if (kind == RgctxDataType.Method && index < model.MethodInstances.Count)
            return new(kind, null, model.MethodInstances[(int)index]);
        if (kind is RgctxDataType.Type or RgctxDataType.Class or RgctxDataType.Array or RgctxDataType.Constrained
            && index < model.RuntimeTypes.Count)
        {
            var type = model.RuntimeTypes[(int)index];
            if (kind != RgctxDataType.Constrained) return new(kind, type, null);
            uint encoded = elf.Word(data + 4);
            int method = (int)((encoded & 0x1ffffffe) >> 1);
            MethodInstance? target = (encoded >> 29) switch
            {
                0 when method is 0 or 1 => null,
                3 when method < model.Methods.Count => new(method, [], []),
                6 when method < model.MethodInstances.Count => model.MethodInstances[method],
                _ => throw new InvalidDataException($"受约束调用的方法编码无效 0x{encoded:x8}"),
            };
            return new(kind, type, target, encoded);
        }
        throw new InvalidDataException($"上下文定义种类或下标无效 {kind}，{index}");
    }
}
