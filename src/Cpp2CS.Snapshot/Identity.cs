namespace Cpp2CS.Snapshot;

/// <summary>块在图内的序号。</summary>
public readonly record struct BlockId(int Index)
{
    public override string ToString() => $"B{Index}";
}

/// <summary>出现的身份：（块，序号）。快照不被改写，身份在快照的生存期内稳定。</summary>
public readonly record struct OccurrenceId(BlockId Block, int Index)
{
    public override string ToString() => $"{Block}.{Index}";
}

/// <summary>边的身份：（源块，出口序号）。起点终点相同的两条边仍是两条。</summary>
public readonly record struct EdgeId(BlockId Source, int Exit)
{
    public override string ToString() => $"{Source}→#{Exit}";
}

/// <summary>程序点：块内第 Index 个出现之前；Index 等于出现数时是块末的终结处。</summary>
public readonly record struct ProgramPoint(BlockId Block, int Index)
{
    public override string ToString() => $"{Block}@{Index}";
}

/// <summary>
/// 内存版本。每次写入、每次调用产生一个版本；块入口的版本由各入边传入。
/// Definition 为 -1 表示块入口的版本，否则是产生它的出现在块内的序号。
/// </summary>
public readonly record struct MemoryVersion(BlockId Block, int Definition)
{
    public bool IsBlockEntry => Definition < 0;
    public override string ToString() => IsBlockEntry ? $"{Block}.入口" : $"{Block}.{Definition}";
}

/// <summary>抽象槽位的类别。前端按目标的调用约定把寄存器映射到槽位，后面各层不出现寄存器名。</summary>
public enum SlotKind : byte
{
    /// <summary>整数或指针实参与结果，按调用约定的次序编号。</summary>
    Integer,
    /// <summary>浮点或向量实参与结果。</summary>
    Vector,
    /// <summary>间接结果的地址（由调用方给出的结果缓冲区）。</summary>
    IndirectResult,
    /// <summary>栈指针。经栈传递的实参是相对它的内存读取。</summary>
    StackPointer,
    /// <summary>线程指针。</summary>
    ThreadPointer,
    /// <summary>被调方保存的寄存器在入口处的值。</summary>
    Preserved,
    /// <summary>返回地址：入口处在链接寄存器里的值；返回出口上是实际返回到的地址。</summary>
    ReturnAddress,
    /// <summary>展开出口上由运行时给出的值（异常对象、选择子）。</summary>
    Unwind,    /// <summary>托管一侧的形参，按签名里的次序编号（实例方法的 this 是第 0 个）。只出现在模板一侧的图里。</summary>
    Managed,
}

/// <summary>抽象槽位。</summary>
public readonly record struct Slot(SlotKind Kind, int Index)
{
    public override string ToString() => $"{Kind}{Index}";
}

/// <summary>实体的类别。</summary>
public enum EntityKind : byte { Type, Method, Field, String, Other }

/// <summary>
/// 实体的不透明身份。内核只比较它是否相等，并原样传递；Key 的取值空间由元数据模型分配和解释。
/// </summary>
public readonly record struct EntityRef(EntityKind Kind, long Key)
{
    public override string ToString() => $"{Kind}#{Key}";
}

/// <summary>规格登记的具名纯函数（运行时属性）的标识。名称与含义在规格里。</summary>
public readonly record struct AttributeId(int Value)
{
    public override string ToString() => $"属性{Value}";
}
