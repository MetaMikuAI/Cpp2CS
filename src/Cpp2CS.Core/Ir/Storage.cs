
namespace Cpp2CS.Ir;

/// <summary>寄存器组。Stack 槽位在栈帧分析之后才出现，Temp 只在单条指令内部使用。</summary>
public enum Bank : byte { Gpr, Vec, Flags, Stack, Temp }

/// <summary>
/// 机器级存储单元。Gpr/Vec 的 Index 是架构寄存器编号；
/// Flags 只有一个（ARM64 NZCV / x64 RFLAGS 的惰性形式）；Stack 的 Index 是相对入口 SP 的字节偏移。
/// </summary>
public readonly record struct Storage(Bank Bank, int Index, int StackWidth = 64)
{
    public static readonly Storage Flags = new(Bank.Flags, 0);

    public static Storage Gpr(int index) => new(Bank.Gpr, index);
    public static Storage Vec(int index) => new(Bank.Vec, index);
    public static Storage Slot(int offset, int width = 64) => new(Bank.Stack, offset, width);
    public static Storage Temp(int index) => new(Bank.Temp, index);

    /// <summary>存储单元的完整宽度（位）。</summary>
    public int Width => Bank switch
    {
        Bank.Gpr => 64,
        Bank.Vec => 128,
        Bank.Flags => 0,
        Bank.Stack => StackWidth,
        _ => 64,
    };

    public override string ToString() => Bank switch
    {
        Bank.Gpr => $"r{Index}",
        Bank.Vec => $"v{Index}",
        Bank.Flags => "flags",
        Bank.Stack => Index < 0 ? $"stk_m{-Index:x}" : $"stk_{Index:x}",
        _ => $"t{Index}",
    };
}
