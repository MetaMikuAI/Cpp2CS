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

/// <summary>运行时操作：L2 惯用法归一后，调用（或一段固定指令序列）所表达的托管语义。</summary>
public enum OpKind : byte
{
    /// <summary>保证类型完成初始化（InitializedTypeInfo / ClassInlines::InitFromCodegen），结果为参数本身。</summary>
    InitClass,
    /// <summary>运行类构造函数（il2cpp_runtime_class_init，cctor 守卫已并入）。</summary>
    RunClassConstructor,
    /// <summary>初始化泛型方法的 RGCTX（结果为参数本身）。</summary>
    InitMethodRgctx,
    NewObject, NewArray, Box, Unbox, IsInst, IsAssignableFrom,
    /// <summary>按数组的实际元素类型检查对象；Arguments 为（对象, 数组），返回原对象或 null。</summary>
    IsInstArrayElement,
    /// <summary>内联的类继承检查（IsInstClass 快速路径）：参数为对象的 Il2CppClass*，结果为 1 表示是 Operand 类型或其子类。</summary>
    TypeCheck,
    /// <summary>条件成立时抛出 Operand 指名的异常（判空、越界之外的检查）。</summary>
    ThrowIf,
    /// <summary>判空：参数为空时抛出 NullReferenceException。</summary>
    NullCheck,
    /// <summary>越界：Arguments 为（索引, 长度）或无法拆分时的条件。</summary>
    BoundsCheck,
    /// <summary>抛出参数中的托管异常对象（il2cpp_raise_exception）。</summary>
    Throw,
    /// <summary>直接构造并抛出 Operand 指名的异常（无参数 helper）。</summary>
    ThrowNew,
    /// <summary>构造 Operand 指名的异常对象并返回（GetException 类 helper）。</summary>
    NewException,
    Rethrow,
    /// <summary>托管引用写入后的写屏障；对应的 Store 紧邻其前。</summary>
    WriteBarrier,
    MemoryBarrier,
    /// <summary>接口方法查找：Arguments 为（对象, 接口类, 槽位），结果为 VirtualInvokeData*。</summary>
    InterfaceInvokeData,
    /// <summary>经 vtable 槽位的虚调用；Operand 为槽位号。</summary>
    CallVirtual,
    /// <summary>泛型虚方法解析：Arguments 为（vtable[method->slot].method, 泛型方法实例），结果为目标 MethodInfo*；Operand 为方法。</summary>
    ResolveGenericVirtual,
    /// <summary>经泛型虚方法解析结果（MethodInfo.virtualMethodPointer）的调用；Operand 为方法。</summary>
    CallGenericVirtual,
    /// <summary>经接口查找结果的调用；Operand 为（接口类型, 槽位）。</summary>
    CallInterface,
    /// <summary>经 Delegate.invoke_impl 的调用。</summary>
    CallDelegate,
    /// <summary>经 MethodInfo.methodPointer 的调用。</summary>
    CallMethodPointer,
    /// <summary>C++ 异常机制（catch 开始/结束、继续展开、终止）。</summary>
    BeginCatch, EndCatch, ResumeUnwind, Terminate,
    /// <summary>FieldInfo 给出的字段地址（共享泛型代码中偏移只在运行时可知）。</summary>
    FieldAddress,
    /// <summary>按元素类的 element_size 计算的数组元素地址。</summary>
    ArrayElementAddress,
    /// <summary>il2cpp_* 导出 API；Operand 为导出名。</summary>
    Export,
    /// <summary>libc 等外部函数（memcpy、数学函数等）；Operand 为符号名。</summary>
    Import,
    /// <summary>逐点证明的 allocate(8)/wrapper+0/__cxa_throw；唯一参数为托管异常对象。</summary>
    ThrowManaged,
    /// <summary>引用原子比较交换：位置、新值、比较值 → 旧引用。</summary>
    CompareExchangeReference,
    /// <summary>按元数据类型复制/清零共享泛型存储；参数为托管地址，Operand 为类型。</summary>
    CopyGenericValue, ClearGenericValue,
    /// <summary>MethodInfo.invoker_method 的已拆包调用，Operand 为方法；最后一个参数为返回存储。</summary>
    InvokeGeneric,
    /// <summary>对象经共享拆箱后按值复制；Operand 为类型，参数为目标存储、对象。</summary>
    UnboxGenericValue,
    /// <summary>共享受约束实例调用；Operand 为方法，参数为约束类型和接收者地址。</summary>
    InvokeConstrainedGeneric,
    /// <summary>两个标量栈出参已显式化的外部调用；Operand 为符号名，Defines 按出参顺序保存结果。</summary>
    ImportOutPair,
}

/// <summary>调用所表达的运行时操作。Operand：类型（TypeRef）、异常名、槽位号等，见 <see cref="OpKind"/>。</summary>
public sealed record RuntimeOp(OpKind Kind, object? Operand)
{
    public override string ToString() => Operand is null ? Kind.ToString() : $"{Kind}<{Operand}>";
}

/// <summary>
/// 调用。Arguments/Results 在提升时为空，由 ABI 阶段根据被调用者签名填入；
/// 提升阶段只描述控制转移本身。
/// </summary>
public sealed record Call(ulong Address, CallKind Kind, Expr Target) : Stmt(Address)
{
    public Expr[] Arguments { get; init; } = [];
    /// <summary>Arguments 各项读自的存储单元（一一对应；ABI 阶段填入）。</summary>
    public Storage[] Sources { get; init; } = [];
    /// <summary>返回值写入的存储单元（ABI 阶段确定）。</summary>
    public Storage[] Results { get; init; } = [];
    /// <summary>SSA 之后 Results 对应的变量（一一对应）。</summary>
    public Variable[] Defines { get; init; } = [];
    /// <summary>L2 识别出的运行时操作；null 表示普通调用。</summary>
    public RuntimeOp? Op { get; init; }
    /// <summary>CallDelegate 的委托对象根；原生 x0 是 method_code，不能用作托管接收者。</summary>
    public Expr? DelegateReceiver { get; init; }
    /// <summary>条件抛出归一后 Address 是分支位置；这里保留真正的原生抛出调用点，供语句级 LSDA 查询。
    /// 只记录来源，不改变生产 CFG 或猜测已删除的异常 phi。</summary>
    public ulong? NativeExceptionSite { get; init; }

    /// <summary>按读自的存储单元索引的实参。</summary>
    public Dictionary<Storage, Expr> ArgumentsBySource()
    {
        var map = new Dictionary<Storage, Expr>();
        for (var i = 0; i < Sources.Length && i < Arguments.Length; i++) map[Sources[i]] = Arguments[i];
        return map;
    }

    public override string ToString() =>
        $"{(Defines.Length > 0 ? string.Join(", ", Defines.Select(d => d?.ToString() ?? "_")) + " = " : Results.Length == 0 ? "" : string.Join(", ", Results) + " = ")}" +
        $"{(Op is null ? Kind.ToString().ToLowerInvariant() + " " + Target : $"op {Op}")}({string.Join(", ", Arguments.Select(a => a.ToString()))})";
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

/// <summary>聚合返回值的一段；Offset 是段在返回值中的字节偏移。</summary>
public sealed record ReturnPiece(int Offset, Expr Value);

public sealed record Return(ulong Address) : Stmt(Address)
{
    public Expr? Value { get; init; }
    public ReturnPiece[] Pieces { get; init; } = [];
    /// <summary>间接返回时，调用方在函数入口提供的结果缓冲区。</summary>
    public Expr? Buffer { get; init; }
    public override string ToString() => Buffer is not null ? $"return buffer {Buffer}"
        : Pieces.Length > 0 ? $"return {{{string.Join(", ", Pieces.Select(p => $"+{p.Offset}: {p.Value}"))}}}"
        : Value is null ? "return" : $"return {Value}";
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
