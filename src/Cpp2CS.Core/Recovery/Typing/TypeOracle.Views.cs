using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Values;

namespace Cpp2CS.Recovery.Typing;

public sealed partial class TypeOracle
{
    /// <summary>字段内部的位片先回到完整标量字段，再做移位与掩码；不跨字段或读取填充。</summary>
    public (Sym Value, TypeRef Type, int Low)? EnclosingScalar(SliceSym slice)
    {
        IEnumerable<(int Bit, int Width, TypeRef Type)> fields = slice.Base is ReadSym read && Parts(read) is { } parts
            ? parts.Select(p => (p.Bit, p.Width, p.Leaf.Type))
            : TypeOf(slice.Base) is DefinitionRef structure && types.Kind(structure) == TypeKind.Struct
                ? types.Leaves(structure).Select(l => (l.Offset * 8, StorageBits(l.Type), l.Type)) : [];
        foreach (var (bit, width, type) in fields)
            if (types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double
                && slice.Low >= bit && slice.Low + slice.Width <= bit + width
                && (slice.Low != bit || slice.Width != width))
                return (values.Syms.Slice(slice.Base, bit, width), type, slice.Low - bit);
        return null;
    }

    /// <summary>合流投影已有完整结构体载体时保留该整体，让后续字段访问共用同一接收者。</summary>
    public (PhiSym Whole, TypeRef WholeType, IReadOnlyList<FieldRef> Path, TypeRef Type)? ProjectedField(PhiSym phi) =>
        phi.Projection is var (whole, low) && low % 8 == 0 && TypeOf(whole) is { } structure && types.Kind(structure) == TypeKind.Struct
        && FieldAt(structure, low / 8 + RuntimeLayout.ObjectHeaderSize, phi.Width, false, false) is var (path, fieldType)
            ? (whole, structure, path, fieldType) : null;

    /// <summary>标量合流的投影复用完整载体，避免为循环中的每一级截断建立新的合流。</summary>
    public (PhiSym Whole, TypeRef Type, int Low)? ProjectedScalar(PhiSym phi) =>
        phi.Width is > 1 and < 64 and not (8 or 16 or 32)
        && phi.Projection is var (whole, low) && ScalarBits(whole, []) && IntegerRepresentation(whole) is var (source, integer)
        && low + phi.Width <= types.Bits(integer) ? (whole, source, low) : null;

    private bool ScalarBits(Sym value, HashSet<Sym> seen)
    {
        value = SymTable.Resolve(value);
        if (!seen.Add(value)) return true;
        return value switch
        {
            ConstSym => true,
            PhiSym phi => phi.Sources.Length > 0 && phi.Sources.All(s => s is not null && ScalarBits(s, seen)),
            ConcatSym concat => concat.Parts.All(p => ScalarBits(p, seen)),
            SliceSym slice => ScalarBits(slice.Base, seen),
            _ => TypeOf(value) is { } type
                && types.Kind(type) is TypeKind.Int or TypeKind.Bool or TypeKind.Float or TypeKind.Double or TypeKind.Pointer,
        };
    }

    /// <summary>标量位型的整数载体；浮点位片先按同宽整数解释，保留 NaN、符号与负零的原始位。</summary>
    public (TypeRef Source, TypeRef Integer)? IntegerRepresentation(Sym value)
    {
        var source = TypeOf(value) ?? (value is PhiSym ? Unconstrained(value.Width) : null);
        if (source is null) return null;
        return types.Kind(source) switch
        {
            TypeKind.Int or TypeKind.Bool or TypeKind.Pointer => (source, source),
            TypeKind.Float => (source, types.Int32),
            TypeKind.Double => (source, types.Int64),
            _ => null,
        };
    }

    /// <summary>类指针所属的对象：引用类型对象偏移 0 处的 64 位读取。</summary>
    public Sym? ClassOwner(Sym klass) => SymTable.Resolve(klass) is ReadSym { Width: 64 } read
        && Decompose(read.Address) is (var root, 0, null, _) && TypeOf(root) is { } type && ManagedTypes.IsReferenceType(type) ? root : null;

    /// <summary>
    /// 托管数组下标的来源：去掉比例寻址丢弃的高位与 32 位扩展，供元素访问和边界检查共同使用。
    /// 这些表示仅在数组的越界语义下等价，不用于非托管指针的字节偏移。
    /// </summary>
    public static Sym ArrayIndex(Sym index)
    {
        while (true)
        {
            index = SymTable.Resolve(index);
            if (index is SliceSym { Low: 0, Width: >= 32 } slice && slice.Base.Width > slice.Width) index = slice.Base;
            else if (index is PhiSym { Projection: { Low: 0 } projection, Width: >= 32 } phi && projection.Whole.Width > phi.Width) index = projection.Whole;
            else if (index is OpSym { Op: { Kind: OperatorKind.Convert } op, Args: [{ Width: 32 } narrow] } && op.Conversion == ConvKind.SignExtend) index = narrow;
            else if (index is ConcatSym { Parts: [{ Width: 32 } low, ConstSym { Value: 0 }] }) index = low;
            else return index;
        }
    }
}
