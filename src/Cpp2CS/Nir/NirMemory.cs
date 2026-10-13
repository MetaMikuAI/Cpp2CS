using System.Collections.Immutable;
using System.Numerics;

namespace Cpp2CS.Nir;

public sealed record NirMemoryResult(ImmutableArray<byte> Bytes, string? Error = null, bool MissingInput = false)
{
    public bool Success => Error is null;
}
public sealed record NirMemoryRegion(string Space, BigInteger Address, int Length, bool Writable);
public sealed record NirAllocation(long Id, string Space, BigInteger Address, int Length);

public sealed class NirMemory
{
    private readonly Dictionary<string, NirMemorySpace> spaces;
    private readonly Dictionary<(string Space, BigInteger Address), byte> bytes = [];
    private readonly List<NirMemoryRegion> regions = [];
    private readonly List<NirAllocation> allocations = [];
    private long allocationId;
    public long Reads { get; private set; }
    public long Writes { get; private set; }

    public NirMemory(NirModule module)
    {
        spaces = module.MemorySpaces.ToDictionary(s => s.Id, StringComparer.Ordinal);
        foreach (var data in module.DataObjects)
        {
            regions.Add(new(data.Space, data.Address, data.Bytes.Length, data.Writable));
            for (var i = 0; i < data.Bytes.Length; i++) bytes[(data.Space, data.Address + i)] = data.Bytes[i];
        }
    }

    // 显式外部存储输入；未提供的字节保持未知，不默认为零。
    public string? Map(NirMemoryRegion region, ImmutableArray<byte> initial = default)
    {
        if (!RangeValid(region.Space, region.Address, region.Length) || !initial.IsDefault && initial.Length > region.Length)
            return "InvalidMemoryInput";
        var space = spaces[region.Space];
        if (region.Address < space.LocalBase + space.LocalLength && region.Address + region.Length > space.LocalBase)
            return "InputOverlapsLocalArena";
        foreach (var prior in regions.Where(r => r.Space == region.Space))
            if (region.Address < prior.Address + prior.Length && region.Address + region.Length > prior.Address && region.Writable != prior.Writable)
                return "ConflictingMemoryPermissions";
        if (!initial.IsDefault)
            for (var i = 0; i < initial.Length; i++)
                if (bytes.TryGetValue((region.Space, region.Address + i), out var existing) && existing != initial[i]) return "ConflictingMemoryInput";
        regions.Add(region);
        if (!initial.IsDefault) for (var i = 0; i < initial.Length; i++) bytes[(region.Space, region.Address + i)] = initial[i];
        return null;
    }

    public NirMemoryResult Read(string space, BigInteger address, int length)
    {
        Reads++;
        var failure = CheckAccess(space, address, length, false, out var mask);
        if (failure is not null) return new([], failure);
        var result = ImmutableArray.CreateBuilder<byte>(length);
        for (var i = 0; i < length; i++)
        {
            if (!bytes.TryGetValue((space, (address + i) & mask), out var value)) return new([], "UninitializedMemory", true);
            result.Add(value);
        }
        return new(result.ToImmutable());
    }

    public NirMemoryResult Write(string space, BigInteger address, ImmutableArray<byte> data)
    {
        Writes++;
        if (data.IsDefault) return new([], "InvalidWriteBytes");
        var failure = CheckAccess(space, address, data.Length, true, out var mask);
        if (failure is not null) return new([], failure);
        for (var i = 0; i < data.Length; i++) bytes[(space, (address + i) & mask)] = data[i];
        return new([]);
    }

    internal NirAllocation? Allocate(string spaceId, int length, int alignment)
    {
        var space = spaces[spaceId];
        var address = Align(space.LocalBase, alignment);
        foreach (var prior in allocations.Where(a => a.Space == spaceId).OrderBy(a => a.Address))
        {
            if (address + length <= prior.Address) break;
            if (address < prior.Address + prior.Length) address = Align(prior.Address + prior.Length, alignment);
        }
        if (length <= 0 || address + length > space.LocalBase + space.LocalLength) return null;
        var result = new NirAllocation(++allocationId, spaceId, address, length);
        allocations.Add(result);
        return result;
    }

    internal void Release(IEnumerable<NirAllocation> owned)
    {
        foreach (var allocation in owned) allocations.Remove(allocation);
        // 地址复用可观察旧字节；释放只结束访问许可，不清零存储。
    }

    // 访问逐字节按地址位宽回绕；先核对全部权限，写入才可提交。
    private string? CheckAccess(string space, BigInteger address, int length, bool write, out BigInteger mask)
    {
        mask = 0;
        if (!spaces.TryGetValue(space, out var definition) || definition.AddressWidth is < 1 or > 4096 || length < 0)
            return "AddressRangeFault";
        mask = (BigInteger.One << definition.AddressWidth) - 1;
        if (address < 0 || address > mask) return "AddressRangeFault";
        for (var i = 0; i < length; i++)
        {
            var at = (address + i) & mask;
            if (allocations.Any(a => a.Space == space && at >= a.Address && at < a.Address + a.Length)) continue;
            var mappings = regions.Where(r => r.Space == space && at >= r.Address && at < r.Address + r.Length).ToArray();
            if (mappings.Length == 0) return "UnmappedMemory";
            if (write && mappings.Any(r => !r.Writable)) return "WritePermissionFault";
        }
        return null;
    }
    private bool RangeValid(string space, BigInteger address, int length) => spaces.TryGetValue(space, out var definition)
        && definition.AddressWidth is >= 1 and <= 4096 && address >= 0 && length >= 0 && address + length <= (BigInteger.One << definition.AddressWidth);
    private static BigInteger Align(BigInteger value, int alignment) => (value + alignment - 1) & ~(new BigInteger(alignment) - 1);
}
