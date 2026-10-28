namespace Cpp2CS.Memory;

/// <summary>同一存储根内的字节区间；地址和位宽的转换只在边界进行。</summary>
internal readonly record struct StorageRange(long Offset, int Size)
{
    public long End => checked(Offset + Size);
    public bool Overlaps(StorageRange other) => Offset < other.End && other.Offset < End;
    public bool Contains(StorageRange other) => Offset <= other.Offset && End >= other.End;
}

/// <summary>栈位置的身份包含函数与生命期，不能仅以物理偏移代替局部变量身份。</summary>
internal sealed record FrameStorage(ulong Function, StorageRange Range, ulong Lifetime);
internal sealed record MemoryVersion(FrameStorage Storage, ulong Write);
