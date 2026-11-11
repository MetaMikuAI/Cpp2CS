using System.Collections.Immutable;

namespace Cpp2CS.Native.Images;

public enum ByteOrder { LittleEndian, BigEndian }
public enum StorageKind { Unmapped, FileContent, ZeroFill }
public enum RelocationKind { Pointer, RelativeDisplacement, ThreadStorage, Resolver, Instruction }
[Flags]
public enum FunctionEvidence { UnwindTable = 1, SymbolTable = 2 }
public enum ClauseKind { Cleanup, Catch, CatchAll, ExceptionSpecification }

/// <summary>所有地址均为相对首选基址的偏移；区间为半开区间。</summary>
/// <summary>Writable 表示加载及重定位完成后的写权限。</summary>
public sealed record ImageRange(ulong Start, ulong Length, StorageKind Storage, bool Executable, bool Writable);
public sealed record AddressInfo(StorageKind Storage, ulong AvailableBytes, bool Executable, bool Writable);
public sealed record ImportSymbol(string Name, string? Library = null, uint? Ordinal = null);
public abstract record PointerTarget
{
    public sealed record Internal(ulong Offset) : PointerTarget;
    public sealed record Import(ImportSymbol Symbol, long Addend = 0) : PointerTarget;
    public sealed record Null : PointerTarget;
    public sealed record Unknown(string Reason) : PointerTarget;
    public sealed record NotPointer(string Reason) : PointerTarget;
}
public sealed record ImageRelocation(ulong Offset, int Width, RelocationKind Kind, PointerTarget Target);
public sealed record ExportSymbol(string Name, PointerTarget Target, uint? Ordinal = null);
public sealed record FunctionSymbol(string Name, ulong Offset, ulong Size);
public sealed record FunctionExtent(ulong Length, FunctionEvidence Evidence);
/// <summary>同起点只保留一条。Length 为证据覆盖的最大长度；冲突的长度和证据完整保存在 Extents。</summary>
public sealed record FunctionRange(ulong Start, ulong Length, FunctionEvidence Evidence)
{
    public ImmutableArray<FunctionExtent> Extents { get; init; } = [new(Length, Evidence)];
}
/// <summary>Catch 的 Matches 为单个类型；ExceptionSpecification 为允许传播的类型集合，空集合表示不允许任何类型。</summary>
public sealed record ExceptionClause(ClauseKind Kind, ImmutableArray<PointerTarget> Matches);
/// <summary>Handler 为空表示直接向外传播；子句顺序与文件的匹配顺序一致。</summary>
public sealed record TryRegion(ulong Start, ulong Length, ulong? Handler, ImmutableArray<ExceptionClause> Clauses);

/// <summary>不可变、可并发查询。字节和整数读取不应用重定位，指针读取应用重定位。
/// 未映射读取抛出 InvalidDataException；零填充读取返回零。</summary>
public interface IImage
{
    ulong PreferredBase { get; }
    int PointerWidth { get; }
    ByteOrder ByteOrder { get; }
    ImmutableArray<ImageRange> Ranges { get; }
    IReadOnlyList<ImageRelocation> Relocations { get; }
    ImmutableArray<ImportSymbol> Imports { get; }
    ImmutableArray<ExportSymbol> Exports { get; }
    /// <summary>可有可无的已定义函数符号证据；符号表被去掉时为空，使用者不得假定存在。地址为相对映像基址的偏移。</summary>
    ImmutableArray<FunctionSymbol> FunctionSymbols { get; }
    ImmutableArray<FunctionRange> Functions { get; }
    ImmutableArray<TryRegion> TryRegions { get; }
    ImmutableArray<string> Diagnostics { get; }
    AddressInfo Query(ulong offset);
    bool IsExecutable(ulong offset, ulong length = 1);
    bool IsWritable(ulong offset, ulong length = 1);
    void ReadBytes(ulong offset, Span<byte> destination);
    ulong ReadUnsigned(ulong offset, int width);
    /// <summary>解析一次间接。目标偏移不保证可解引用，权限与映射由 Query 回答；无重定位的非零位置无关槽返回 NotPointer。</summary>
    PointerTarget ReadPointer(ulong offset);
}
