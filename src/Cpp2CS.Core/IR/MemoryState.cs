using System.Collections.Immutable;

namespace Cpp2CS.IR;

public enum RegionKind { Stack, Object, Global, Unknown }
public sealed record RegionId(string Identity, RegionKind Kind);
public sealed record StorageAddress(RegionId Region, long Offset);
public sealed record MemoryWrite(StorageAddress Address, Bits Value);

// 持久化字节存储。地址不随写入变化，内容版本随状态变化。
public sealed class MemoryState
{
    private readonly ImmutableDictionary<StorageAddress, Bits> bytes;
    public string Version { get; }
    public MemoryState(string version) : this(version, ImmutableDictionary<StorageAddress, Bits>.Empty) { }
    private MemoryState(string version, ImmutableDictionary<StorageAddress, Bits> bytes) { Version = version; this.bytes = bytes; }
    public Bits Load(StorageAddress address, int size)
    {
        ArgumentOutOfRangeException.ThrowIfNegativeOrZero(size);
        return BitOps.Concat(Enumerable.Range(0, size).Select(i => ReadByte(address with { Offset = checked(address.Offset + i) })));
    }
    private Bits ReadByte(StorageAddress address) => bytes.GetValueOrDefault(address) ??
        new UnknownBits($"{Version}:{address.Region}:{address.Offset}", "未定义或被不明写入影响的内存", 8);
    public MemoryState Store(string version, StorageAddress address, Bits value)
    {
        if (value.Width <= 0 || value.Width % 8 != 0) throw new ArgumentException("内存访问必须使用整字节");
        var updated = bytes;
        for (var i = 0; i < value.Width / 8; i++)
            updated = updated.SetItem(address with { Offset = checked(address.Offset + i) }, BitOps.Slice(value, i * 8, 8));
        return new(version, updated);
    }
    // 未确定别名范围时，全部存储失效；不能假设栈地址从未逃逸。
    public MemoryState Invalidate(string version) => new(version);
    public static MemoryState Merge(string block, params MemoryState[] incoming)
    {
        if (incoming.Length == 0) throw new ArgumentException("合流需要前驱");
        var keys = incoming.SelectMany(x => x.bytes.Keys).Distinct();
        return new(block, keys.ToImmutableDictionary(k => k, k => BitOps.Phi(block, incoming.Select(m => m.ReadByte(k)))));
    }
}
