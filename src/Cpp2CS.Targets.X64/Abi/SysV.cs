using System.Collections.Immutable;
using Cpp2CS.Native;
using Cpp2CS.Native.Abi;

namespace Cpp2CS.Targets.X64.Abi;

/// <summary>小端 LP64 SysV psABI §3.2.3；平凡聚合、整数、指针、二进制 float/double。</summary>
public sealed class SysV : IAbiClassifier
{
    private enum Eightbyte { None, Integer, Floating }

    public AbiClassification Classify(CSignature signature)
    {
        if (CTypes.Validate(signature) is { } why) return AbiClassification.Failure(why);
        var resultClasses = Classes(signature.ReturnType);
        var integer = resultClasses is null ? 1 : 0;
        var floating = 0;
        var stack = 0;
        AbiReturn result;
        if (resultClasses is null)
            result = new([], new(0, 8, new(SlotKind.Integer)), new(0, 8, new(SlotKind.Integer)));
        else
        {
            int ri = 0, rf = 0;
            result = new(Pieces(signature.ReturnType, resultClasses, ref ri, ref rf));
        }
        var args = ImmutableArray.CreateBuilder<AbiValue>();
        foreach (var type in signature.Parameters)
        {
            var classes = Classes(type);
            // 两种槽池同时预留；不足时撤销整个实参，后面的实参仍可用剩余槽。
            if (classes is not null && integer + classes.Count(c => c == Eightbyte.Integer) <= 6
                && floating + classes.Count(c => c == Eightbyte.Floating) <= 8)
                args.Add(new(Pieces(type, classes, ref integer, ref floating)));
            else
            {
                stack = CTypes.Round(stack, Math.Max(8, type.Alignment));
                args.Add(new([new(0, type.Size, new(SlotKind.ArgumentArea, stack))]));
                stack += CTypes.Round(type.Size, 8);
            }
        }
        return new(new(args.ToImmutable(), result, CTypes.Round(stack, 16), 16), null);
    }

    private static Eightbyte[]? Classes(CType type)
    {
        // 无向量时超过两个八字节必为 MEMORY；未对齐字段同样为 MEMORY。
        if (type.Size > 16) return null;
        var classes = new Eightbyte[CTypes.Round(type.Size, 8) / 8];
        foreach (var leaf in CTypes.Leaves(type))
        {
            if (leaf.Offset % leaf.Type.Alignment != 0) return null;
            var kind = leaf.Type is CFloat ? Eightbyte.Floating : Eightbyte.Integer;
            for (var i = leaf.Offset / 8; i < (leaf.Offset + leaf.Type.Size + 7) / 8; i++)
                // 合并：INTEGER 优先；NO_CLASS 不影响已有类。
                classes[i] = classes[i] == Eightbyte.Integer || kind == Eightbyte.Integer ? Eightbyte.Integer : kind;
        }
        return classes;
    }

    private static ImmutableArray<AbiPiece> Pieces(CType type, Eightbyte[] classes, ref int integer, ref int floating)
    {
        var pieces = ImmutableArray.CreateBuilder<AbiPiece>();
        for (var i = 0; i < classes.Length; i++)
        {
            if (classes[i] == Eightbyte.None) continue;
            var slot = classes[i] == Eightbyte.Integer
                ? new AbstractSlot(SlotKind.Integer, integer++) : new AbstractSlot(SlotKind.Floating, floating++);
            pieces.Add(new(i * 8, Math.Min(8, type.Size - i * 8), slot));
        }
        return pieces.ToImmutable();
    }
}
