using System.Collections.Immutable;
using Cpp2CS.Images;
using Cpp2CS.Ir;

namespace Cpp2CS.Native;

public readonly record struct BlockId(int Id);
public readonly record struct EdgeId(int Id);
public sealed record EntrySeed(ulong Address, string Evidence);
public enum RegionBoundaryKind
{
    Unmapped, NotExecutable, NotFileBacked, Truncated, Unaligned, InvalidEncoding,
    Unsupported, CodeRelocation, Budget, IndirectTarget, Call, Return, ExceptionBoundary
}
public sealed record RegionBoundary(RegionBoundaryKind Kind, string Reason);
public sealed record RegionEdge(EdgeId Id, BlockId Source, BlockId? Target,
    MirSuccessor Successor, RegionBoundary? Boundary);
// 第一版每块只容纳一条指令；重叠的 x64 解码入口具有独立块身份。
public sealed record RegionBlock(BlockId Id, ulong Address, MirInstruction? Instruction,
    RegionBoundary? Stop, ImmutableArray<RegionEdge> Edges);
public sealed record RegionEntry(EntrySeed Seed, BlockId Block);
public sealed record RegionRevision(string Revision, string ImageId, Architecture Architecture,
    string ProfileId, string SemanticsVersion, ImmutableArray<RegionEntry> Entries,
    ImmutableArray<RegionBlock> Blocks);

public interface IRegionInstructionSource
{
    string ImageId { get; }
    Architecture Architecture { get; }
    InstructionDecodeResult Decode(ulong address);
}
