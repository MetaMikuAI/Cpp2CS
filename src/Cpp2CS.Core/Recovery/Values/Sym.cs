using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Recovery.Values;

/// <summary>
/// 符号值：机器值在 IL 中是什么。节点由 <see cref="SymTable"/> 创建并驻留：结构相同的节点只有一个实例，
/// 因此子节点按引用比较即可。读取、调用结果、调用写出与 φ 按身份区分。宽度以位为单位。
/// 原子是 IL 层的值（参数、常量、读取、调用结果、运算、φ 等）；切片与拼接只描述位来自哪个原子的哪一段。
/// </summary>
public abstract class Sym(int width)
{
    public int Id { get; internal set; }
    public int Width { get; } = width;

    /// <summary>不含切片与拼接的 IL 值。</summary>
    public virtual bool IsAtom => true;

    public abstract override string ToString();
}

/// <summary>IL 参数整体；Index -1 为 this。结构体参数的宽度是整个值的位数。</summary>
public sealed class ArgSym(int index, int width) : Sym(width)
{
    public int Index { get; } = index;
    public override bool Equals(object? obj) => obj is ArgSym o && o.Index == Index && o.Width == Width;
    public override int GetHashCode() => HashCode.Combine(1, Index, Width);
    public override string ToString() => Index < 0 ? "this" : $"arg{Index}";
}

/// <summary>不超过 64 位的常量；更宽的常量是常量片的拼接。</summary>
public sealed class ConstSym(ulong value, int width) : Sym(width)
{
    public ulong Value { get; } = value;
    public long Signed => Width >= 64 ? unchecked((long)Value) : (long)(Value << (64 - Width)) >> (64 - Width);
    public override bool Equals(object? obj) => obj is ConstSym o && o.Value == Value && o.Width == Width;
    public override int GetHashCode() => HashCode.Combine(2, Value, Width);
    public override string ToString() => Width == 1 ? (Value != 0 ? "true" : "false") : $"0x{Value:x}:{Width}";
}

/// <summary>没有定义的位：填充、未初始化的栈内容、ABI 不保证的高位。下降时不能作为值使用。</summary>
public sealed class UndefSym(int width) : Sym(width)
{
    public override bool Equals(object? obj) => obj is UndefSym o && o.Width == Width;
    public override int GetHashCode() => HashCode.Combine(3, Width);
    public override string ToString() => $"undef:{Width}";
}

/// <summary>模型表达不了的值，带原因；下降时成为洞。</summary>
public sealed class UnknownSym(string reason, int width) : Sym(width)
{
    public string Reason { get; } = reason;
    public override bool Equals(object? obj) => obj is UnknownSym o && o.Reason == Reason && o.Width == Width;
    public override int GetHashCode() => HashCode.Combine(4, Reason, Width);
    public override string ToString() => $"unknown<{Reason}>";
}

/// <summary>元数据实体（类、方法、字段、字符串、静态字段块等），来自 L2 的 <see cref="Symbol"/>。</summary>
public sealed class EntitySym(Symbol symbol) : Sym(64)
{
    public Symbol Symbol { get; } = symbol;
    public override bool Equals(object? obj) => obj is EntitySym o && o.Symbol.Equals(Symbol);
    public override int GetHashCode() => HashCode.Combine(5, Symbol);
    public override string ToString() => Symbol.ToString();
}

/// <summary>相对入口 SP 的帧地址。</summary>
public sealed class FrameSym(long offset) : Sym(64)
{
    public long Offset { get; } = offset;
    public override bool Equals(object? obj) => obj is FrameSym o && o.Offset == Offset;
    public override int GetHashCode() => HashCode.Combine(6, Offset);
    public override string ToString() => Offset < 0 ? $"&frame-{-Offset:x}" : $"&frame+{Offset:x}";
}

/// <summary>调用或运行时操作的结果。Index 0 是 IL 返回值整体；签名未知时按结果寄存器的序号区分。</summary>
public sealed class ResultSym(Call site, int index, int width) : Sym(width)
{
    public Call Site { get; } = site;
    public int Index { get; } = index;
    public override string ToString() => Index == 0 ? $"ret@{Site.Address:x}" : $"ret{Index}@{Site.Address:x}";
}

/// <summary>调用经指针实参写入的值：<see cref="Argument"/> 为机器签名中的值序号（含结果缓冲区）。</summary>
public sealed class OutSym(Call site, int argument, int width) : Sym(width)
{
    public Call Site { get; } = site;
    public int Argument { get; } = argument;
    public override string ToString() => $"out{(Argument == Facts.MachineSignature.ReturnIndex ? "ret" : Argument.ToString())}@{Site.Address:x}";
}

/// <summary>某程序点对内存的一次读取。Site 是读取所在语句，Ordinal 区分同一语句中的多次读取。</summary>
public sealed class ReadSym(Stmt site, int ordinal, Sym address, int width) : Sym(width)
{
    public Stmt Site { get; } = site;
    public int Ordinal { get; } = ordinal;
    public Sym Address { get; } = address;
    public override string ToString() => $"[{Address}]:{Width}@{Site.Address:x}";
}

/// <summary>Base 的 [Low, Low+Width) 位。Base 是原子。</summary>
public sealed class SliceSym(Sym @base, int low, int width) : Sym(width)
{
    public Sym Base { get; } = @base;
    public int Low { get; } = low;
    public override bool IsAtom => false;
    public override bool Equals(object? obj) => obj is SliceSym o && ReferenceEquals(o.Base, Base) && o.Low == Low && o.Width == Width;
    public override int GetHashCode() => HashCode.Combine(7, Base.Id, Low, Width);
    public override string ToString() => $"{Base}[{Low}:{Width}]";
}

/// <summary>低位在前的拼接。各部分不是拼接，至少两个。</summary>
public sealed class ConcatSym(Sym[] parts) : Sym(parts.Sum(p => p.Width))
{
    public Sym[] Parts { get; } = parts;
    public override bool IsAtom => false;
    public override bool Equals(object? obj) => obj is ConcatSym o && o.Parts.AsSpan().SequenceEqual(Parts);
    public override int GetHashCode()
    {
        var hash = new HashCode();
        hash.Add(8);
        foreach (var part in Parts) hash.Add(part.Id);
        return hash.ToHashCode();
    }
    public override string ToString() => $"{{{string.Join(" | ", Parts.Select(p => p.ToString()))}}}";
}

public enum OperatorKind : byte { Binary, Unary, Compare, Convert, Select, And, Or, Not, Intrinsic }

/// <summary>IL 层的运算。Code 是对应机器枚举（BinOp、UnOp、Cond、ConvKind）的值；Intrinsic 的名称在 Name 中。</summary>
public readonly record struct Operator(OperatorKind Kind, byte Code, string? Name = null)
{
    public static Operator Of(BinOp op) => new(OperatorKind.Binary, (byte)op);
    public static Operator Of(UnOp op) => new(OperatorKind.Unary, (byte)op);
    public static Operator Of(Cond cond) => new(OperatorKind.Compare, (byte)cond);
    public static Operator Of(ConvKind kind) => new(OperatorKind.Convert, (byte)kind);
    public BinOp Binary => (BinOp)Code;
    public UnOp Unary => (UnOp)Code;
    public Cond Cond => (Cond)Code;
    public ConvKind Conversion => (ConvKind)Code;

    public override string ToString() => Kind switch
    {
        OperatorKind.Binary => Binary.ToString(),
        OperatorKind.Unary => Unary.ToString(),
        OperatorKind.Compare => Cond.ToString(),
        OperatorKind.Convert => Conversion.ToString(),
        OperatorKind.Intrinsic => Name!,
        _ => Kind.ToString(),
    };
}

public sealed class OpSym(Operator op, Sym[] args, int width) : Sym(width)
{
    public Operator Op { get; } = op;
    public Sym[] Args { get; } = args;
    public override bool Equals(object? obj) => obj is OpSym o && o.Op == Op && o.Width == Width && o.Args.AsSpan().SequenceEqual(Args);
    public override int GetHashCode()
    {
        var hash = new HashCode();
        hash.Add(Op);
        hash.Add(Width);
        foreach (var arg in Args) hash.Add(arg.Id);
        return hash.ToHashCode();
    }
    public override string ToString() => $"{Op}({string.Join(", ", Args.Select(a => a.ToString()))})";
}

/// <summary>
/// 块入口的合流。Sources 与块的前驱一一对应。Origin 为来源的机器 φ 目标或帧单元；
/// 投影（Projection）是另一个 φ 的一段，来源为各来源的同一段。
/// Forward 不为 null 时这个 φ 是平凡的，等于 Forward。
/// </summary>
public sealed class PhiSym(Block block, object origin, int width) : Sym(width)
{
    public Block Block { get; } = block;
    public object Origin { get; } = origin;
    public Sym?[] Sources { get; } = new Sym?[block.Predecessors.Count];
    public (PhiSym Whole, int Low)? Projection { get; init; }
    public Sym? Forward { get; internal set; }
    public override string ToString() => Projection is { } p ? $"φ{p.Whole.Id}[{p.Low}:{Width}]" : $"φ{Id}";
}
