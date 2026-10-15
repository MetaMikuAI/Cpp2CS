using Cpp2CS.Arm64;
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

public sealed class Arm64Machine(ImageDocument image) : IMachine
{
    public Architecture Architecture => Architecture.Arm64;
    public ImageDocument Image { get; } = image;

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

    /// <summary>被链接器移到补丁桩里的指令数（统计用）。</summary>
    public int PatchedInstructions { get; private set; }

    private bool Readable(ulong address) => (address & 3) == 0 && Image.IsExecutable(address) && Image.ReadUpTo(address, 4).Length == 4;

    public int Lift(ulong address, List<Stmt> output)
    {
        if (!Readable(address)) return 0;
        var word = Image.ReadU32(address);
        if (Patched(address, word) is { } moved)
        {
            PatchedInstructions++;
            foreach (var stmt in moved) output.Add(stmt with { Address = address });
            return 4;
        }
        Arm64Lifter.Lift(address, word, output);
        return 4;
    }

    /// <summary>
    /// Cortex-A53 勘误 843419 补丁：链接器把 adrp 之后的访存指令换成 b stub，stub 为“原指令; b 原地址+4”。
    /// 二进制证据：桩区里成对出现的 ldr + b 回跳（见 docs）。只接受与位置无关的原指令
    /// （在两个不同地址提升结果相同），此时把它当作原地址上的指令。
    /// </summary>
    private List<Stmt>? Patched(ulong address, uint word)
    {
        if ((word & 0xFC000000) != 0x14000000) return null;
        var offset = (long)((ulong)(word & 0x03FFFFFF) << 38) >> 36;
        var stub = address + (ulong)offset;
        if (!Readable(stub) || !Readable(stub + 4)) return null;
        var back = Image.ReadU32(stub + 4);
        if ((back & 0xFC000000) != 0x14000000 || stub + 4 + (ulong)((long)((ulong)(back & 0x03FFFFFF) << 38) >> 36) != address + 4) return null;
        var here = new List<Stmt>();
        var elsewhere = new List<Stmt>();
        var moved = Image.ReadU32(stub);
        Arm64Lifter.Lift(stub, moved, here);
        Arm64Lifter.Lift(stub ^ 0x40000000, moved, elsewhere);
        if (here.Count == 0 || here.Any(s => s is Jump or Branch or Call or Return or IndirectJump or Trap or Opaque)) return null;
        return here.Select(s => s.ToString()).SequenceEqual(elsewhere.Select(s => s.ToString())) ? here : null;
    }
}
