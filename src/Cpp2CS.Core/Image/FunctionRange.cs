
namespace Cpp2CS.Image;

/// <summary>函数边界的来源。符号候选与展开表证据不能等同。</summary>
public enum BoundaryEvidence
{
    /// <summary>ARM64 .eh_frame 的 FDE，边界由展开表直接给出。</summary>
    EhFrame,

    /// <summary>x64 PE 的 .pdata RUNTIME_FUNCTION，边界由展开表直接给出。</summary>
    Pdata,

    /// <summary>只有相邻符号地址作为候选终点，未经展开表核实。</summary>
    SymbolCandidate,

    /// <summary>没有展开表条目、但被代码或重定位当作入口引用的目标；终点为下一个已知边界，需由控制流确认。</summary>
    Reference,

    /// <summary>ELF PLT 桩（PLT0 之后每 16 字节一个），由桩的固定指令序列确认。</summary>
    PltStub,
}

/// <summary>
/// LSDA 中的一条 call-site 区间。LandingPad 为 0 表示该区间内抛出的异常直接向外传播。
/// IL2CPP 的 catch 子句在 C++ 层统一捕获 Il2CppExceptionWrapper，托管类型筛选在落地块的代码里完成。
/// </summary>
public sealed record ExceptionRegion(ulong Start, ulong End, ulong LandingPad)
{
    public ulong ActionOffset { get; init; }
    public ExceptionAction[] Actions { get; init; } = [];
}

/// <summary>
/// 一个函数的代码范围。Start 与 End 都是半开区间 [Start, End)。
/// </summary>
public sealed record FunctionRange(ulong Start, ulong End, BoundaryEvidence Evidence, string? Note)
{
    public ExceptionRegion[] ExceptionRegions { get; init; } = [];

    /// <summary>x64：通过 UNW_FLAG_CHAININFO 链到本函数的其他代码片段（已按地址排序）。</summary>
    public FunctionRange[] Fragments { get; init; } = [];

    /// <summary>x64：UNWIND_INFO 中的异常处理例程（UNW_FLAG_EHANDLER/UHANDLER），没有时为 null。</summary>
    public ulong? Handler { get; init; }

    /// <summary>x64：紧随处理例程 RVA 之后的语言相关数据的地址。</summary>
    public ulong? HandlerData { get; init; }

    public ulong Size => End - Start;

    public bool Contains(ulong address) => address >= Start && address < End;

    public string Describe() => $"0x{Start:x8}..0x{End:x8} [{Evidence}{(Note is null ? "" : ": " + Note)}]";

}
