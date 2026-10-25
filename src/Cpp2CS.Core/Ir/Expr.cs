namespace Cpp2CS.Ir;

public enum BinOp : byte
{
    Add, Sub, Mul, SDiv, UDiv, SRem, URem, And, Or, Xor, Shl, LShr, AShr, Ror,
    MulHighS, MulHighU,
    FAdd, FSub, FMul, FDiv, FMin, FMax,
}

public enum UnOp : byte
{
    Neg, Not, Clz, Cls, Rbit, PopCount,
    /// <summary>整个操作数的字节序反转。</summary>
    Bswap,
    /// <summary>每 16 位/32 位内部的字节序反转（ARM64 rev16/rev32）。</summary>
    Bswap16, Bswap32,
    FNeg, FAbs, FSqrt,
    /// <summary>浮点取整（结果仍为浮点）。</summary>
    FFloor, FCeil, FTrunc, FRoundEven, FRoundAway, FRoundCurrent,
}

/// <summary>比较条件。整数比较区分有符号/无符号；浮点比较的 Unordered 情况单独列出。</summary>
public enum Cond : byte
{
    Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge,
    FEq, FNe, FLt, FLe, FGt, FGe, FUnordered, FOrdered,
    // 无序或比较：ARM64 FCMP 之后的 b.lt/b.le/b.hi 等条件在 NaN 时为真
    FUlt, FUle, FUgt, FUge, FUeq, FUne,
    Neg, NotNeg, Overflow, NoOverflow,
}

public enum ConvKind : byte
{
    ZeroExtend, SignExtend, Truncate,
    SIntToFloat, UIntToFloat, FloatToSInt, FloatToUInt, FloatToFloat,
    /// <summary>同宽度位重解释（整数寄存器与浮点寄存器之间的 fmov/movq）。</summary>
    Bitcast,
}

/// <summary>惰性标志位的来源运算。</summary>
public enum FlagKind : byte
{
    /// <summary>L - R（cmp/subs）。</summary>
    Sub,
    /// <summary>L + R（cmn/adds）。</summary>
    Add,
    /// <summary>逻辑结果与 0 比较（tst/ands/x64 test 等）；R 为参与 and 的另一个操作数，或者为 null 表示 L 本身。</summary>
    Logic,
    /// <summary>浮点比较（fcmp/ucomiss/comisd）。</summary>
    FloatCompare,
}

/// <summary>
/// 表达式。宽度以位为单位；条件表达式宽度为 1。
/// Unknown 是一等值：无法恢复的部分在这里显式保留，绝不被当作 0。
/// </summary>
public abstract record Expr(int Width)
{
    public static Const C(ulong value, int width) => new(width == 64 ? value : value & Mask(width), width);

    public static ulong Mask(int width) => width >= 64 ? ulong.MaxValue : (1UL << width) - 1;
}

public sealed record Const(ulong Value, int Width) : Expr(Width)
{
    public long Signed => Width >= 64 ? unchecked((long)Value) : (long)(Value << (64 - Width)) >> (64 - Width);
    public override string ToString() => Width == 1 ? (Value != 0 ? "true" : "false") : $"0x{Value:x}";
}

/// <summary>读取机器存储单元（SSA 之前）。Width 小于存储宽度时为低位截取。</summary>
public sealed record Read(Storage Storage, int Width) : Expr(Width)
{
    public override string ToString() => Width == Storage.Width ? Storage.ToString() : $"{Storage}.{Width}";
}

/// <summary>读取 SSA 变量（SSA 之后）。Width 小于变量宽度时为低位截取。</summary>
public sealed record Use(Variable Variable, int Width) : Expr(Width)
{
    public override string ToString() => Width == Variable.Width ? Variable.ToString() : $"{Variable}.{Width}";
}

public sealed record Load(Expr Address, int Width) : Expr(Width)
{
    public override string ToString() => $"[{Address}]:{Width}";
}

public sealed record Binary(BinOp Op, Expr Left, Expr Right, int Width) : Expr(Width)
{
    public override string ToString() => $"({Left} {Op} {Right})";
}

public sealed record Unary(UnOp Op, Expr Operand, int Width) : Expr(Width)
{
    public override string ToString() => $"{Op}({Operand})";
}

public sealed record Compare(Cond Cond, Expr Left, Expr Right) : Expr(1)
{
    public override string ToString() => $"({Left} {Cond} {Right})";
}

public sealed record Convert(ConvKind Kind, Expr Operand, int Width) : Expr(Width)
{
    public override string ToString() => $"{Kind}{Width}({Operand})";
}

public sealed record Select(Expr Condition, Expr True, Expr False, int Width) : Expr(Width)
{
    public override string ToString() => $"({Condition} ? {True} : {False})";
}

/// <summary>布尔连接（ccmp 链等）。宽度为 1。</summary>
public sealed record Logical(bool IsAnd, Expr Left, Expr Right) : Expr(1)
{
    public override string ToString() => $"({Left} {(IsAnd ? "&&" : "||")} {Right})";
}

public sealed record Not(Expr Operand) : Expr(1)
{
    public override string ToString() => $"!{Operand}";
}

/// <summary>位段提取：Operand 的 [Low, Low+Width) 位。</summary>
public sealed record Extract(Expr Operand, int Low, int Width) : Expr(Width)
{
    public override string ToString() => $"{Operand}[{Low}:{Width}]";
}

/// <summary>位段插入：把 Value 写入 Base 的 [Low, Low+Value.Width) 位，其余位保持不变。</summary>
public sealed record Insert(Expr Base, Expr Value, int Low) : Expr(Base.Width)
{
    public override string ToString() => $"insert({Base}, {Value}@{Low})";
}

/// <summary>惰性标志位：由某次比较/运算产生，由条件分支等消费者按条件码解释。</summary>
public sealed record Flags(FlagKind Kind, Expr Left, Expr? Right, int OperandWidth) : Expr(0)
{
    public override string ToString() => $"flags.{Kind}({Left}, {Right})";
}

/// <summary>按条件码解释标志位。Code 的含义由架构决定，见 FlagCondition。</summary>
public sealed record TestFlags(Expr FlagsValue, FlagCondition Code) : Expr(1)
{
    public override string ToString() => $"{Code}({FlagsValue})";
}

/// <summary>ARM64 ccmp/fccmp：条件成立时取 Taken 的标志，否则取立即数 NZCV。</summary>
public sealed record ConditionalFlags(Expr Condition, Expr Taken, byte Nzcv) : Expr(0)
{
    public override string ToString() => $"ccmp({Condition}, {Taken}, #{Nzcv})";
}

/// <summary>相对入口 SP 的栈地址（帧分析之后出现）。</summary>
public sealed record FrameAddress(long Offset) : Expr(64)
{
    public override string ToString() => Offset < 0 ? $"&frame_m{-Offset:x}" : $"&frame_{Offset:x}";
}

/// <summary>函数入口时某存储单元的值（参数寄存器、callee-saved 寄存器、入口 SP 等）。</summary>
public sealed record Entry(Storage Storage) : Expr(Storage.Width)
{
    public override string ToString() => $"in_{Storage}";
}

/// <summary>没有通用表达式形式的机器操作（系统寄存器、向量运算等），按名称保留。</summary>
public sealed record Intrinsic(string Name, Expr[] Arguments, int Width) : Expr(Width)
{
    public override string ToString() => $"{Name}({string.Join(", ", Arguments.Select(a => a.ToString()))})";
    public bool Equals(Intrinsic? other) => other is not null && Name == other.Name && Width == other.Width && Arguments.AsSpan().SequenceEqual(other.Arguments);
    public override int GetHashCode() => HashCode.Combine(Name, Width, Arguments.Length);
}

/// <summary>已识别实体的种类。</summary>
public enum SymbolKind : byte
{
    /// <summary>Il2CppClass*（TypeInfo 槽位的值）。Value 为 TypeRef。</summary>
    Class,
    /// <summary>const Il2CppType*。Value 为 TypeRef。</summary>
    Type,
    /// <summary>const MethodInfo*。Value 为 MethodRef。</summary>
    Method,
    /// <summary>FieldInfo*。Value 为 FieldRef。</summary>
    Field,
    /// <summary>Il2CppString*（字符串字面量）。Value 为 string。</summary>
    String,
    /// <summary>类型的静态字段块（Il2CppClass.static_fields）。Value 为 TypeRef。</summary>
    StaticFields,
    /// <summary>方法或类的 RGCTX 数组（MethodInfo.rgctx_data / Il2CppClass.rgctx_data）。Value 为 RgctxTable。</summary>
    Rgctx,
    /// <summary>RGCTX 中的 constrained 调用条目。Value 为 (TypeRef, MethodRef)。</summary>
    Constrained,
}

/// <summary>
/// 一张 RGCTX 表：Image/Token 为方法（0x06）或类型（0x02）定义，Owner 为显示名；
/// TypeArguments/MethodArguments 为代入的实参，为 null 时条目保留泛型参数形式（共享代码自身的上下文）。
/// </summary>
public sealed record RgctxTable(string Image, uint Token, string Owner, IReadOnlyList<Model.TypeRef>? TypeArguments, IReadOnlyList<Model.TypeRef>? MethodArguments)
{
    public override string ToString() => TypeArguments is null && MethodArguments is null ? $"{Owner}（自身）" : Owner;
}

/// <summary>
/// 已识别的程序实体：值在运行时确定，但它指向的托管实体由事实层唯一确定（如元数据槽位初始化之后的值）。
/// 作为叶子参与表达式；求值器不能求值。
/// </summary>
public sealed record Symbol(SymbolKind Kind, object Value) : Expr(64)
{
    public override string ToString() => Kind == SymbolKind.String ? $"\"{Value}\"" : $"{Kind}<{Value}>";
}

public sealed record Unknown(string Reason, int Width) : Expr(Width)
{
    public override string ToString() => $"unknown<{Reason}>";
}

/// <summary>
/// 统一的条件码（ARM64 的 cond 字段语义）。x64 的 jcc/setcc/cmovcc 在提升时映射到这里。
/// </summary>
public enum FlagCondition : byte
{
    Eq, Ne, Hs, Lo, Mi, Pl, Vs, Vc, Hi, Ls, Ge, Lt, Gt, Le, Al, Nv,
    /// <summary>x64 PF=1（浮点比较的无序结果）。</summary>
    Parity,
    /// <summary>x64 PF=0。</summary>
    NoParity,
}
