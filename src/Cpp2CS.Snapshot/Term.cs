using System.Collections.Immutable;
using System.Text;

namespace Cpp2CS.Snapshot;

/// <summary>项的种类。</summary>
public enum TermKind : byte
{
    /// <summary>常量，位宽不超过 128。</summary>
    Constant,
    /// <summary>未定义：填充位和被破坏的位。未定义的位不是值。</summary>
    Undefined,
    /// <summary>入口参数，按抽象槽位区分。</summary>
    EntryParameter,
    /// <summary>块参数，按（块，序号）区分。</summary>
    BlockParameter,
    /// <summary>出现的结果：读取的结果、调用的各结果槽。</summary>
    Result,
    /// <summary>运算。</summary>
    Operation,
    /// <summary>切片：取操作数从 Offset 位起的 Width 位。</summary>
    Slice,
    /// <summary>拼接：操作数按从低位到高位的次序排列。</summary>
    Concat,
    /// <summary>选择：条件为 1 取第二个操作数，否则取第三个。</summary>
    Select,
    /// <summary>实体：类、方法、字段、字符串。由事实层引入。</summary>
    Entity,
    /// <summary>规格登记的具名纯函数（运行时属性）。由事实层引入。</summary>
    Attribute,
}

/// <summary>运算符。整数运算按位型定义，对有无符号的解释写在运算符里；浮点运算作用在 IEEE 754 位型上。</summary>
public enum Op : ushort
{
    None,
    Add, Sub, Mul, UDiv, SDiv, URem, SRem, Neg,
    And, Or, Xor, Not,
    /// <summary>移位量与被移位的值同宽；移位量不小于位宽时，逻辑移位得 0，算术右移得符号位的复制。</summary>
    Shl, LShr, AShr,
    /// <summary>符号扩展到项的位宽。</summary>
    SignExtend,
    /// <summary>比较，结果 1 位。其余方向与严格性由这三个加取反表示。</summary>
    Eq, Ult, Slt,
    /// <summary>加法的无符号进位、有符号溢出，减法的有符号溢出，结果 1 位。</summary>
    AddCarry, AddOverflow, SubOverflow,
    /// <summary>乘积的高半部分。</summary>
    UMulHigh, SMulHigh,
    CountLeadingZeros, CountTrailingZeros, PopCount, ByteSwap, BitReverse,
    FAdd, FSub, FMul, FDiv, FRem, FNeg, FAbs, FSqrt,
    /// <summary>浮点比较，结果 1 位；任一操作数为 NaN 时 FEq、FLt、FLe 为 0，FUnordered 为 1。</summary>
    FEq, FLt, FLe, FUnordered,
    /// <summary>浮点格式之间的转换，目标格式由项的位宽给出。</summary>
    FConvert,
    SToF, UToF,
    /// <summary>浮点转整数，向零舍入；越界与 NaN 时饱和（NaN 得 0）。</summary>
    FToSSaturate, FToUSaturate,
    /// <summary>浮点转有符号整数，向零舍入；越界与 NaN 时得最小负数。</summary>
    FToSIndefinite,
    /// <summary>目标自定义的纯运算，以代码区分。相同的代码与操作数给出相同的值，除此之外不作解释。</summary>
    Opaque,
}

/// <summary>
/// 项：值的唯一表示。项只由 <see cref="TermPool"/> 构造，构造时规范化并驻留，结构相同就是同一个实例。
/// </summary>
public sealed class Term
{
    public TermKind Kind { get; }
    /// <summary>位宽。</summary>
    public int Width { get; }
    /// <summary>池内的驻留序号，按首次构造的次序分配。只在同一个池内有意义。</summary>
    public int Id { get; internal set; } = -1;
    /// <summary>由结构决定的散列，与构造次序、图号无关。可交换运算的操作数按它排序；散列相同时按驻留序号。</summary>
    public ulong StructuralHash { get; }
    /// <summary>项里是否含未定义的位。靠“两个操作数是同一个项”得出结论的规则，要求此项为假。</summary>
    public bool HasUndefined { get; }
    public Op Op { get; }
    public ImmutableArray<Term> Operands { get; }
    internal UInt128 Payload { get; }
    internal int A { get; }
    internal int B { get; }
    internal int C { get; }
    internal int D { get; }

    internal Term(TermKind kind, int width, ImmutableArray<Term> operands, Op op = Op.None, UInt128 payload = default,
        int a = 0, int b = 0, int c = 0, int d = 0)
    {
        Kind = kind;
        Width = width;
        Operands = operands;
        Op = op;
        Payload = payload;
        A = a; B = b; C = c; D = d;
        bool undefined = kind == TermKind.Undefined;
        ulong h = 0xcbf29ce484222325UL;
        h = Mix(h, (ulong)kind); h = Mix(h, (ulong)width); h = Mix(h, (ulong)op);
        h = Mix(h, (ulong)payload); h = Mix(h, (ulong)(payload >> 64));
        // 图号不进入结构散列：同一段代码在不同的图号下，可交换运算的操作数次序相同。
        bool tagged = kind is TermKind.EntryParameter or TermKind.BlockParameter or TermKind.Result;
        h = Mix(h, tagged ? 0u : (uint)a); h = Mix(h, (uint)b); h = Mix(h, (uint)c); h = Mix(h, (uint)d);
        foreach (var o in operands)
        {
            undefined |= o.HasUndefined;
            h = Mix(h, o.StructuralHash);
        }
        HasUndefined = undefined;
        StructuralHash = h;
    }

    private static ulong Mix(ulong h, ulong v)
    {
        h ^= v;
        h *= 0x100000001b3UL;
        return h ^ (h >> 29);
    }

    /// <summary>常量的值。</summary>
    public UInt128 Value => Kind == TermKind.Constant ? Payload : throw Wrong(TermKind.Constant);
    public bool IsConstant => Kind == TermKind.Constant;
    public bool IsZero => Kind == TermKind.Constant && Payload == UInt128.Zero;
    /// <summary>切片的起始位。</summary>
    public int Offset => Kind == TermKind.Slice ? A : throw Wrong(TermKind.Slice);
    /// <summary>所属的图号：0 是被恢复方法的快照，其余由模板一侧的图使用。</summary>
    public int Graph => Kind is TermKind.EntryParameter or TermKind.BlockParameter or TermKind.Result ? A : throw Wrong(TermKind.BlockParameter);
    /// <summary>入口参数的槽位。</summary>
    public Slot Slot => Kind == TermKind.EntryParameter ? new((SlotKind)B, C) : throw Wrong(TermKind.EntryParameter);
    /// <summary>块参数所属的块，或出现的结果所属的块。</summary>
    public BlockId Block => Kind is TermKind.BlockParameter or TermKind.Result ? new(B) : throw Wrong(TermKind.BlockParameter);
    /// <summary>块参数的序号。</summary>
    public int ParameterIndex => Kind == TermKind.BlockParameter ? C : throw Wrong(TermKind.BlockParameter);
    /// <summary>产生这个结果的出现。</summary>
    public OccurrenceId Occurrence => Kind == TermKind.Result ? new(new(B), C) : throw Wrong(TermKind.Result);
    /// <summary>结果槽的序号。</summary>
    public int ResultIndex => Kind == TermKind.Result ? D : throw Wrong(TermKind.Result);
    public EntityRef Entity => Kind == TermKind.Entity ? new((EntityKind)A, unchecked((long)(ulong)Payload)) : throw Wrong(TermKind.Entity);
    public AttributeId Attribute => Kind == TermKind.Attribute ? new(A) : throw Wrong(TermKind.Attribute);
    /// <summary>目标自定义运算的代码。</summary>
    public int OpaqueCode => Kind == TermKind.Operation && Op == Op.Opaque ? A : throw Wrong(TermKind.Operation);

    private InvalidOperationException Wrong(TermKind expected) => new($"项的种类是 {Kind}，不是 {expected}");

    internal bool SameStructure(Term other)
    {
        if (Kind != other.Kind || Width != other.Width || Op != other.Op || Payload != other.Payload
            || A != other.A || B != other.B || C != other.C || D != other.D || Operands.Length != other.Operands.Length)
            return false;
        for (int i = 0; i < Operands.Length; i++)
            if (!ReferenceEquals(Operands[i], other.Operands[i])) return false;
        return true;
    }

    public override string ToString()
    {
        var text = new StringBuilder();
        Print(text, 0);
        return text.ToString();
    }

    private void Print(StringBuilder text, int depth)
    {
        if (depth > 12) { text.Append('…'); return; }
        switch (Kind)
        {
            case TermKind.Constant: text.Append("0x").Append(Payload.ToString("x")).Append(':').Append(Width); return;
            case TermKind.Undefined: text.Append("未定义:").Append(Width); return;
            case TermKind.EntryParameter: text.Append("入口.").Append(Slot).Append(':').Append(Width); return;
            case TermKind.BlockParameter: text.Append(Block).Append(".参").Append(ParameterIndex).Append(':').Append(Width); return;
            case TermKind.Result: text.Append("结果(").Append(Occurrence).Append('#').Append(ResultIndex).Append("):").Append(Width); return;
            case TermKind.Entity: text.Append(Entity); return;
            case TermKind.Slice: Operands[0].Print(text, depth + 1); text.Append('[').Append(A).Append("+:").Append(Width).Append(']'); return;
        }
        text.Append(Kind switch
        {
            TermKind.Concat => "拼接",
            TermKind.Select => "选择",
            TermKind.Attribute => Attribute.ToString(),
            _ => Op == Op.Opaque ? $"Opaque{A}" : Op.ToString(),
        });
        if (Kind == TermKind.Operation && Op == Op.SignExtend) text.Append(':').Append(Width);
        text.Append('(');
        for (int i = 0; i < Operands.Length; i++)
        {
            if (i > 0) text.Append(", ");
            Operands[i].Print(text, depth + 1);
        }
        text.Append(')');
    }
}
