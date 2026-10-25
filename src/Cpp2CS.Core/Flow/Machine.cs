using Cpp2CS.Arm64;
using Cpp2CS.Facts;
using Cpp2CS.Images;
using Cpp2CS.Ir;

namespace Cpp2CS.Flow;

/// <summary>调用约定中与数据流有关的事实。</summary>
public sealed class CallingConvention
{
    public required Storage StackPointer { get; init; }
    public required Storage[] IntegerArguments { get; init; }
    public required Storage[] FloatArguments { get; init; }
    /// <summary>大结构返回值的地址寄存器（ARM64 x8）；x64 通过第一个参数传递，为 null。</summary>
    public Storage? IndirectResult { get; init; }
    public required Storage[] IntegerResults { get; init; }
    public required Storage[] FloatResults { get; init; }
    /// <summary>调用后整体失效的存储单元（不含结果寄存器以外的特殊处理）。</summary>
    public required Storage[] Clobbered { get; init; }
    /// <summary>调用后只有低 64 位保留的向量寄存器（ARM64 v8-v15）。</summary>
    public Storage[] LowHalfPreserved { get; init; } = [];
}

/// <summary>指令集相关的提升与约定。</summary>
public interface IMachine
{
    Architecture Architecture { get; }
    ImageDocument Image { get; }
    CallingConvention Convention { get; }
    /// <summary>提升 address 处的一条指令并返回其长度；地址不可读时返回 0。</summary>
    int Lift(ulong address, List<Stmt> output);
}

/// <summary>ARM64 机器：指令字经 <see cref="CodeMap.Word"/> 读取，勘误 843419 补丁位置得到的是链接前的原指令。</summary>
public sealed class Arm64Machine(CodeMap code) : IMachine
{
    public Architecture Architecture => Architecture.Arm64;
    public ImageDocument Image => Code.Image;
    public CodeMap Code { get; } = code;

    public CallingConvention Convention { get; } = new()
    {
        StackPointer = Storage.Gpr(Arm64Lifter.Sp),
        IntegerArguments = Enumerable.Range(0, 8).Select(Storage.Gpr).ToArray(),
        FloatArguments = Enumerable.Range(0, 8).Select(Storage.Vec).ToArray(),
        IndirectResult = Storage.Gpr(8),
        IntegerResults = [Storage.Gpr(0), Storage.Gpr(1)],
        FloatResults = Enumerable.Range(0, 4).Select(Storage.Vec).ToArray(),
        Clobbered = [.. Enumerable.Range(0, 19).Select(Storage.Gpr), Storage.Gpr(Arm64Lifter.Lr),
            .. Enumerable.Range(0, 8).Select(Storage.Vec), .. Enumerable.Range(16, 16).Select(Storage.Vec), Storage.Flags],
        LowHalfPreserved = Enumerable.Range(8, 8).Select(Storage.Vec).ToArray(),
    };

    public int Lift(ulong address, List<Stmt> output)
    {
        if ((address & 3) != 0 || Code.Word(address) is not { } word) return 0;
        Arm64Lifter.Lift(address, word, output);
        return 4;
    }
}
