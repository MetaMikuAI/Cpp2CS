using System.Collections.Immutable;

namespace Cpp2CS.Spec.Runtime;

/// <summary>聚合体（托管值类型）在调用约定里的放法。</summary>
public enum AggregatePlacement : byte
{
    /// <summary>
    /// 依次占若干个通用寄存器槽：值按从低地址装入寄存器的方式放，每个槽装 SlotBytes 个字节，最后一个槽只用低位，其余位未规定。
    /// </summary>
    IntegerSlots,
    /// <summary>同质浮点聚合体：每个成员占一个向量槽的低位。</summary>
    VectorPerMember,
    /// <summary>
    /// 按引用：实参由调用方复制到它分配的内存里，实参换成这块内存的地址，占一个通用寄存器槽；
    /// 返回值写进调用方给出的缓冲区，缓冲区的地址在间接结果槽里。
    /// </summary>
    Reference,
    /// <summary>成员未知，放法不能判定。</summary>
    Unknown,
}

/// <summary>聚合体按字段递归展开之后的一个基本成员：在值里的位偏移、存储位宽、是否浮点。</summary>
public readonly record struct AggregateMember(int OffsetBits, int Bits, bool Float);

/// <summary>
/// 值类型实参与返回值的传递方式。il2cpp 把托管值类型写成 C++ 的平凡结构体并按值传递与返回
/// （生成代码的签名形如 int32_t M(Pair_t a, const RuntimeMethod* method)），放法由目标的过程调用标准决定。
/// 标量的放法不在这里：整数、引用、地址依次占通用寄存器槽，浮点依次占向量槽。
/// </summary>
/// <param name="Target">目标。</param>
/// <param name="IntegerSlots">传递实参的通用寄存器个数。</param>
/// <param name="VectorSlots">传递实参的向量寄存器个数。</param>
/// <param name="SlotBytes">一个通用寄存器槽的字节数。</param>
/// <param name="MaximumInRegistersBytes">不是同质浮点聚合体时，按值放进寄存器的聚合体的最大字节数；更大的按引用。</param>
/// <param name="MaximumHomogeneousMembers">同质浮点聚合体的最多成员数。</param>
/// <param name="Source">出处。</param>
public sealed record AggregateConvention(string Target, int IntegerSlots, int VectorSlots, int SlotBytes, int MaximumInRegistersBytes,
    int MaximumHomogeneousMembers, string Source)
{
    /// <summary>
    /// AAPCS64（Arm 64 位过程调用标准）。§6.8.2 参数传递：B.2 同质浮点聚合体原样传递，C.2 每个成员占一个向量寄存器；
    /// B.3 大于 16 字节的聚合体换成调用方副本的地址；B.4 其余聚合体的大小向上取到 8 字节的倍数，
    /// C.10 放进连续的通用寄存器，如同从 8 字节对齐的地址按次序装入，未用的部分未规定。
    /// §6.9 结果返回：能按第一个实参放进寄存器的类型，在同样的寄存器里返回；否则写进调用方给出的内存，地址在 x8（间接结果槽）。
    /// 同质浮点聚合体：至多 4 个成员，展开后的基本成员都是同一种浮点类型（§5.9.5）。
    /// </summary>
    public static AggregateConvention Aapcs64 { get; } = new("arm64-v8a", IntegerSlots: 8, VectorSlots: 8, SlotBytes: 8,
        MaximumInRegistersBytes: 16, MaximumHomogeneousMembers: 4,
        "AAPCS64 §5.9.5 同质聚合体，§6.8.2 参数传递 B.2、B.3、B.4、C.2、C.10、C.11，§6.9 结果返回");

    /// <summary>按大小与成员判定放法。规则的先后照 §6.8.2：先认同质浮点聚合体，再按大小。</summary>
    public AggregatePlacement Classify(int sizeBits, ImmutableArray<AggregateMember> members)
    {
        if (members.IsDefaultOrEmpty || sizeBits <= 0) return AggregatePlacement.Unknown;
        var first = members[0];
        if (members.All(m => m.Float && m.Bits == first.Bits))
        {
            // 成员都是同一种浮点类型。成员之间或末尾有空隙时（显式布局），生成的 C++ 结构体另有填充成员，这里不判定。
            bool packed = sizeBits == members.Length * first.Bits;
            for (int i = 0; packed && i < members.Length; i++) packed = members[i].OffsetBits == i * first.Bits;
            if (!packed) return AggregatePlacement.Unknown;
            if (members.Length <= MaximumHomogeneousMembers) return AggregatePlacement.VectorPerMember;
        }
        return sizeBits > MaximumInRegistersBytes * 8 ? AggregatePlacement.Reference : AggregatePlacement.IntegerSlots;
    }

    /// <summary>按通用寄存器槽放时占几个槽：大小向上取到槽的整数倍。</summary>
    public int SlotsFor(int sizeBits) => (sizeBits + SlotBytes * 8 - 1) / (SlotBytes * 8);
}
