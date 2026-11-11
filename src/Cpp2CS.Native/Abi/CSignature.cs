using System.Collections.Immutable;

namespace Cpp2CS.Native.Abi;

/// <summary>已完成语言映射的平凡 C 类型；大小、对齐和偏移均以字节计。聚合成员不得重叠。</summary>
public abstract record CType(int Size, int Alignment);
public sealed record CInteger(int Bits) : CType(Bits / 8, Bits / 8);
public sealed record CPointer(int Bits) : CType(Bits / 8, Bits / 8);
/// <summary>IEEE 二进制浮点；其他浮点格式不能仅以位宽冒充。</summary>
public sealed record CFloat(int Bits) : CType(Bits / 8, Bits / 8);
public sealed record CField(int Offset, CType Type);
public sealed record CAggregate(int ByteSize, int ByteAlignment, ImmutableArray<CField> Fields)
    : CType(ByteSize, ByteAlignment);
/// <summary>只允许用作聚合成员；顶层 C 数组必须先按语言规则映射。</summary>
public sealed record CArray(CType Element, int Count) : CType(checked(Element.Size * Count), Element.Alignment);
public sealed record CVoid() : CType(0, 1);
public sealed record CSignature(ImmutableArray<CType> Parameters, CType ReturnType, bool IsVariadic = false);

/// <summary>所有位置均相对值起点或槽起点。ArgumentArea 的 Position 是栈实参区字节偏移。</summary>
public sealed record AbiPiece(int ValueOffset, int Length, AbstractSlot Slot, int SlotOffset = 0);
public enum UnusedBitRule { Unspecified }
/// <summary>片段之外的槽位比特不受保证；片段覆盖的聚合填充字节也没有值语义。</summary>
public sealed record AbiValue(ImmutableArray<AbiPiece> Pieces, AbiPiece? CopyAddress = null)
{
    public UnusedBitRule UnusedBits => UnusedBitRule.Unspecified;
}
/// <summary>BufferAddress 属于输入槽；ReturnedAddress 属于结果槽。间接返回没有直接值片段。</summary>
public sealed record AbiReturn(ImmutableArray<AbiPiece> Pieces, AbiPiece? BufferAddress = null,
    AbiPiece? ReturnedAddress = null)
{
    public UnusedBitRule UnusedBits => UnusedBitRule.Unspecified;
}
/// <summary>Parameters[i] 与签名第 i 个形参对应；栈大小含末尾对齐，不含按引用传递的副本存储。</summary>
public sealed record SlotAssignment(ImmutableArray<AbiValue> Parameters, AbiReturn Return,
    int StackSize, int StackAlignment);
public sealed record AbiClassification(SlotAssignment? Assignment, string? Problem)
{
    public bool Success => Assignment is not null;
    public static AbiClassification Failure(string reason) => new(null, reason);
}
public interface IAbiClassifier
{
    AbiClassification Classify(CSignature signature);
}

/// <summary>分类入口的结构验证；不支持的格式显式返回原因。递归深度和大小限制是资源边界。</summary>
public static class CTypes
{
    public static string? Validate(CSignature signature)
    {
        if (signature.IsVariadic) return "不支持可变参数";
        if (signature.Parameters.IsDefault) return "形参列表未初始化";
        if (ValidateType(signature.ReturnType, true, false, 0) is { } result) return "返回值：" + result;
        for (var i = 0; i < signature.Parameters.Length; i++)
            if (ValidateType(signature.Parameters[i], false, false, 0) is { } reason) return $"形参 {i}：{reason}";
        return null;
    }

    private static string? ValidateType(CType type, bool allowVoid, bool member, int depth)
    {
        if (depth > 64) return "类型嵌套超过 64 层";
        if (type.Size is < 0 or > 1048576 || type.Alignment is <= 0 or > 16
            || (type.Alignment & (type.Alignment - 1)) != 0) return "大小或对齐不受支持（最大 1 MiB、对齐最大 16）";
        switch (type)
        {
            case CVoid: return allowVoid ? null : "void 不是形参或成员类型";
            case CInteger i: return i.Bits is 8 or 16 or 32 or 64 or 128 ? null : "不支持的整数位宽";
            case CPointer p: return p.Bits == 64 ? null : "只支持 64 位指针";
            case CFloat f: return f.Bits is 32 or 64 ? null : "只支持二进制 32/64 位浮点";
            case CArray a:
                if (!member || a.Count <= 0) return "数组只允许作为非空聚合成员";
                return ValidateType(a.Element, false, true, depth + 1);
            case CAggregate a:
                if (a.Fields.IsDefault || a.Size % a.Alignment != 0) return "聚合成员未初始化或大小未对齐";
                var end = 0;
                foreach (var field in a.Fields.OrderBy(f => f.Offset))
                {
                    if (ValidateType(field.Type, false, true, depth + 1) is { } why) return why;
                    if (field.Offset < end || field.Offset < 0 || field.Offset > a.Size - field.Type.Size)
                        return "成员越界或重叠；联合类型尚未支持";
                    end = field.Offset + field.Type.Size;
                }
                return null;
            default: return "未知 C 类型（向量与非平凡对象尚未支持）";
        }
    }

    public static int Round(int value, int alignment) => checked((value + alignment - 1) / alignment * alignment);

    /// <summary>只枚举有值的叶子；不枚举聚合填充。</summary>
    public static IEnumerable<CField> Leaves(CType type, int offset = 0)
    {
        switch (type)
        {
            case CAggregate aggregate:
                foreach (var field in aggregate.Fields)
                    foreach (var leaf in Leaves(field.Type, offset + field.Offset)) yield return leaf;
                break;
            case CArray array:
                for (var i = 0; i < array.Count; i++)
                    foreach (var leaf in Leaves(array.Element, offset + i * array.Element.Size)) yield return leaf;
                break;
            case CVoid: break;
            default: yield return new(offset, type); break;
        }
    }
}
