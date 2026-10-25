using Cpp2CS.Facts;
using Cpp2CS.Model;

namespace Cpp2CS.Tests.Execution;

internal sealed partial class World
{
    private readonly HashSet<ulong> padding = [];
    private readonly Dictionary<(int, TypeRef), byte[]> structReturns = new();
    private readonly Dictionary<(int Call, int Argument, TypeRef Type), byte[]> callWrites = new();

    /// <summary>和返回值共用同一个 World：含引用的后值必须只分配一次，不能在两侧分别生成对象。</summary>
    public byte[] CallWriteBytes(int ordinal, int argument, TypeRef type)
    {
        if (!callWrites.TryGetValue((ordinal, argument, type), out var value))
            callWrites.Add((ordinal, argument, type), value = ValueBytes(type, $"call{ordinal}.out{argument}"));
        return value;
    }

    public bool Observable(ulong address) => Compared(address) && !padding.Contains(address);

    /// <summary>仅排除已由 L1 布局证明的结构体填充；普通对象/运行时数据的比较规则不变。</summary>
    public void RegisterValue(ulong address, TypeRef type)
    {
        if (!Aapcs64Classifier.IsStruct(type)) return;
        var bytes = new bool[StorageSize(type)];
        foreach (var leaf in Index.StructAbi.Classifier.Leaves(type))
            for (var i = 0; i < leaf.Size; i++) bytes[leaf.Offset + i] = true;
        for (var i = 0; i < bytes.Length; i++) if (!bytes[i]) padding.Add(address + (ulong)i);
    }

    public void RegisterObject(ulong address, TypeRef type)
    {
        for (var current = type as DefinitionRef; current is not null;
             current = current.Definition.BaseType?.Substitute(current.Arguments, []) as DefinitionRef)
            if (Layouts.Of(current) is { } layout)
                foreach (var field in layout.Fields) RegisterValue(address + (ulong)field.Offset, field.Type);
    }

    public byte[] ValueBytes(TypeRef type, string key)
    {
        if (!Aapcs64Classifier.IsStruct(type)) return StructAbi.Bytes(Value(type, key, 0), StorageSize(type));
        var result = new byte[StorageSize(type)];
        foreach (var leaf in Index.StructAbi.Classifier.Leaves(type))
            StructAbi.Bytes(Value(leaf.Type, $"{key}.{leaf.Path}", 0), leaf.Size).CopyTo(result, leaf.Offset);
        return result;
    }

    public byte[] ReturnBytes(int ordinal, TypeRef type)
    {
        if (!Aapcs64Classifier.IsStruct(type)) return StructAbi.Bytes(ReturnValue(ordinal, type), StorageSize(type));
        if (!structReturns.TryGetValue((ordinal, type), out var bytes))
            structReturns.Add((ordinal, type), bytes = ValueBytes(type, $"return{ordinal}"));
        return bytes;
    }
}
