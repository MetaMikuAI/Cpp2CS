namespace Cpp2CS.Ir;

/// <summary>SSA 变量：某个存储单元的一个版本。Version 0 表示函数入口值。</summary>
public sealed record Variable(Storage Storage, int Version)
{
    public int Width => Storage.Width;
    public override string ToString() => Version == 0 ? $"in_{Storage}" : $"{Storage}_{Version}";
}

/// <summary>
/// 语句。每条机器指令提升为若干语句；Address 记录来源指令，便于回溯证据。
/// </summary>
public abstract record Stmt(ulong Address);

/// <summary>写存储单元。Value 窄于存储单元时高位清零（ARM64 W/S/D 写、x64 32 位写、VEX 标量写）；
/// 需要保留高位的写入（x64 8/16 位写、SSE 标量写）由提升器显式构造 Insert 表达式。</summary>
public sealed record Assign(ulong Address, Storage Target, Expr Value) : Stmt(Address)
{
    public override string ToString() => $"{Target} = {Value}";
}

/// <summary>SSA 形式的定义。</summary>
public sealed record Define(ulong Address, Variable Target, Expr Value) : Stmt(Address)
{
    public override string ToString() => $"{Target} = {Value}";
}

public sealed record Phi(ulong Address, Variable Target, Variable[] Sources) : Stmt(Address)
{
    public override string ToString() => $"{Target} = phi({string.Join(", ", Sources.Select(s => s.ToString()))})";
}

public sealed record Store(ulong Address, Expr Target, Expr Value) : Stmt(Address)
{
    public override string ToString() => $"[{Target}]:{Value.Width} = {Value}";
}

public enum CallKind : byte { Direct, Indirect, Tail, TailIndirect }

/// <summary>
/// 调用。Arguments/Results 在提升时为空，由 ABI 阶段根据被调用者签名填入；
/// 提升阶段只描述控制转移本身。
/// </summary>
public sealed record Call(ulong Address, CallKind Kind, Expr Target) : Stmt(Address)
{
    public Expr[] Arguments { get; init; } = [];
    /// <summary>返回值写入的存储单元（ABI 阶段确定）。</summary>
    public Storage[] Results { get; init; } = [];
    public override string ToString() =>
        $"{(Results.Length == 0 ? "" : string.Join(", ", Results) + " = ")}{Kind.ToString().ToLowerInvariant()} {Target}({string.Join(", ", Arguments.Select(a => a.ToString()))})";
}

public sealed record Jump(ulong Address, ulong Target) : Stmt(Address)
{
    public override string ToString() => $"goto 0x{Target:x}";
}

public sealed record Branch(ulong Address, Expr Condition, ulong Target, ulong Fallthrough) : Stmt(Address)
{
    public override string ToString() => $"if {Condition} goto 0x{Target:x} else 0x{Fallthrough:x}";
}

/// <summary>寄存器间接跳转（跳转表等），目标集合由后续分析恢复。</summary>
public sealed record IndirectJump(ulong Address, Expr Target) : Stmt(Address)
{
    public ulong[] Targets { get; init; } = [];
    public override string ToString() => $"goto *{Target}";
}

public sealed record Return(ulong Address) : Stmt(Address)
{
    public Expr? Value { get; init; }
    public override string ToString() => Value is null ? "return" : $"return {Value}";
}

/// <summary>不返回的陷入（brk/ud2/int3）。</summary>
public sealed record Trap(ulong Address, string Kind) : Stmt(Address)
{
    public override string ToString() => $"trap {Kind}";
}

/// <summary>提升失败的指令。保留原文，令输出总是存在且可追溯；写入集合未知，后续分析必须视为屏障。</summary>
public sealed record Opaque(ulong Address, string Text) : Stmt(Address)
{
    public override string ToString() => $"opaque \"{Text}\"";
}

/// <summary>对语义无影响但值得保留的指令（屏障、预取、hint）。</summary>
public sealed record Nop(ulong Address, string Text) : Stmt(Address)
{
    public override string ToString() => $"nop {Text}";
}
