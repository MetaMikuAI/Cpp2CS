using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;

namespace Cpp2CS.Targets.Arm64.Abi;

/// <summary>小端 LP64 基本 PCS。依据 AAPCS64 2025Q1 §6.8.2、§6.9；不含变参和向量。</summary>
public sealed class Aapcs64 : IAbiClassifier
{
    public AbiClassification Classify(CSignature signature)
    {
        if (CTypes.Validate(signature) is { } why) return AbiClassification.Failure(why);
        if (signature.Parameters.Append(signature.ReturnType).Any(HasAdjustedAlignment))
            return AbiClassification.Failure("显式提高聚合对齐需要成员对齐修饰信息，当前类型描述尚不支持");
        var cursor = new Cursor();
        var args = signature.Parameters.Select(t => Allocate(t, cursor)).ToImmutableArray();
        var returned = Allocate(signature.ReturnType, new Cursor());
        var result = returned.CopyAddress is null ? new AbiReturn(returned.Pieces)
            : new AbiReturn([], new(0, 8, new(SlotKind.IndirectResult)));
        return new(new(args, result, CTypes.Round(cursor.Stack, 16), 16), null);
    }

    // B.6 的自然对齐与整体对齐不同；没有语言层修饰信息时不猜测复制品的对齐。
    private static bool HasAdjustedAlignment(CType type) => type switch
    {
        CAggregate a => a.Fields.Length > 0 && a.Alignment > a.Fields.Max(f => f.Type.Alignment)
            || a.Fields.Any(f => HasAdjustedAlignment(f.Type)),
        CArray a => HasAdjustedAlignment(a.Element),
        _ => false,
    };

    private sealed class Cursor { public int Integer; public int Floating; public int Stack; }

    private static AbiValue Allocate(CType type, Cursor cursor)
    {
        if (type is CVoid || type.Size == 0) return new([]);
        var hfa = Homogeneous(type);
        if (type is CFloat || hfa.Length != 0)
        {
            var leaves = type is CFloat ? new[] { new CField(0, type) } : hfa;
            if (cursor.Floating + leaves.Length <= 8)
                return new(leaves.Select(f => new AbiPiece(f.Offset, f.Type.Size,
                    new(SlotKind.Floating, cursor.Floating++))).ToImmutableArray());
            cursor.Floating = 8; // C.3–C.6：失败后关闭浮点槽池。
            return Stack(type.Size, Math.Max(8, type.Alignment), false, cursor);
        }
        // B.3 优先于 B.4：大 HFA 仍按值；其他大聚合改传副本地址。
        var indirect = type is CAggregate && type.Size > 16;
        var size = indirect ? 8 : type.Size;
        var alignment = indirect ? 8 : type.Alignment;
        if (alignment == 16) cursor.Integer = CTypes.Round(cursor.Integer, 2);
        var count = CTypes.Round(size, 8) / 8;
        if (cursor.Integer + count <= 8)
        {
            var pieces = Enumerable.Range(0, count).Select(i => new AbiPiece(i * 8,
                Math.Min(8, size - i * 8), new(SlotKind.Integer, cursor.Integer++))).ToImmutableArray();
            return indirect ? new([], pieces[0]) : new(pieces);
        }
        cursor.Integer = 8; // C.11–C.17：整个实参入栈，后续整数也入栈。
        return Stack(size, Math.Max(8, alignment), indirect, cursor);
    }

    private static AbiValue Stack(int size, int alignment, bool indirect, Cursor cursor)
    {
        cursor.Stack = CTypes.Round(cursor.Stack, alignment);
        var piece = new AbiPiece(0, size, new(SlotKind.ArgumentArea, cursor.Stack));
        cursor.Stack += CTypes.Round(size, 8);
        return indirect ? new([], piece) : new([piece]);
    }

    private static CField[] Homogeneous(CType type)
    {
        if (type is not CAggregate) return [];
        var leaves = CTypes.Leaves(type).Take(5).OrderBy(f => f.Offset).ToArray();
        if (leaves.Length is < 1 or > 4 || leaves[0].Type is not CFloat floating
            || leaves.Any(f => f.Type != floating)) return [];
        // §5.10.5：完成布局后恰好由同类浮点成员组成，不含额外填充。
        return type.Size == leaves.Length * floating.Size
            && leaves.Select((f, i) => f.Offset == i * floating.Size).All(b => b) ? leaves : [];
    }
}
