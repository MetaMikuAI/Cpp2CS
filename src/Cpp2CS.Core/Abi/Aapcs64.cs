using Cpp2CS.Model;

namespace Cpp2CS.Abi;

public enum ShapeKind { Void, Integer, Float, Composite, HomogeneousFloat, Unknown }
// 机器签名形状独立于托管泛型实参，用于共享代码的 ABI 分类。
public sealed record AbiShape(ShapeKind Kind, int Size, int Alignment, int ElementSize = 0, int ElementCount = 0)
{
    public static AbiShape Integer(int size = 8) => new(ShapeKind.Integer, size, size);
    public static AbiShape Float(int size) => new(ShapeKind.Float, size, size);
    public static AbiShape Composite(int size, int alignment = 8) => new(ShapeKind.Composite, size, alignment);
    public static AbiShape Hfa(int elementSize, int count) => new(ShapeKind.HomogeneousFloat, elementSize * count, elementSize, elementSize, count);
    public static AbiShape Void => new(ShapeKind.Void, 0, 1);
    public static AbiShape Unknown => new(ShapeKind.Unknown, 0, 1);
}
public sealed record NativeSignature(Sequence<AbiShape> Arguments, AbiShape Return, Evidence Evidence, bool Variadic = false);
public abstract record Location;
public sealed record RegisterLocation(string Name, int BitOffset = 0) : Location;
public sealed record StackLocation(int Offset) : Location;
public sealed record AbiPiece(Location Location, int ValueOffset, int Size);
public sealed record AbiValue(AbiShape Shape, Sequence<AbiPiece> Pieces, bool Indirect = false);
public sealed record CallLayout(Sequence<AbiValue> Arguments, AbiValue Return, int StackBytes, Evidence Evidence);
public sealed record AbiResult(CallLayout? Layout, string? Unsupported)
{
    public bool IsSupported => Layout is not null;
}

public static class Aapcs64
{
    public static AbiResult Classify(NativeSignature signature)
    {
        if (signature.Variadic) return new(null, "尚不支持可变参数 ABI");
        if (!Supported(signature.Return, true) || signature.Arguments.Any(s => !Supported(s, false)))
            return new(null, "布局未知或超出当前 AAPCS64 标量/聚合支持范围");
        var ngrn = 0;
        var nsrn = 0;
        var stack = 0;
        var arguments = new List<AbiValue>();
        foreach (var original in signature.Arguments)
        {
            var indirect = original.Kind == ShapeKind.Composite && original.Size > 16;
            var shape = indirect ? AbiShape.Integer() : original;
            var pieces = new List<AbiPiece>();
            if (shape.Kind is ShapeKind.Float or ShapeKind.HomogeneousFloat)
            {
                var count = shape.Kind == ShapeKind.Float ? 1 : shape.ElementCount;
                var element = shape.Kind == ShapeKind.Float ? shape.Size : shape.ElementSize;
                if (nsrn + count <= 8)
                {
                    for (var i = 0; i < count; i++) pieces.Add(new(new RegisterLocation($"V{nsrn++}"), i * element, element));
                }
                else
                {
                    nsrn = 8;
                    AddStack(shape, pieces, ref stack);
                }
            }
            else
            {
                if (shape.Alignment == 16) ngrn = Align(ngrn, 2);
                var count = (shape.Size + 7) / 8;
                if (ngrn + count <= 8)
                {
                    for (var i = 0; i < count; i++) pieces.Add(new(new RegisterLocation($"X{ngrn++}"), i * 8, Math.Min(8, shape.Size - i * 8)));
                }
                else
                {
                    ngrn = 8;
                    AddStack(shape, pieces, ref stack);
                }
            }
            arguments.Add(new(original, new(pieces), indirect));
        }
        return new(new(new(arguments), Return(signature.Return), Align(stack, 16), signature.Evidence), null);
    }
    private static bool Supported(AbiShape s, bool allowVoid) => s.Kind switch
    {
        ShapeKind.Void => allowVoid && s.Size == 0,
        ShapeKind.Integer => s.Size is 1 or 2 or 4 or 8 or 16 && s.Alignment == s.Size,
        ShapeKind.Float => s.Size is 4 or 8 && s.Alignment == s.Size,
        ShapeKind.Composite => s.Size > 0 && s.Alignment is 1 or 2 or 4 or 8 or 16,
        ShapeKind.HomogeneousFloat => s.ElementSize is 4 or 8 && s.ElementCount is >= 1 and <= 4 &&
            s.Size == s.ElementSize * s.ElementCount && s.Alignment == s.ElementSize,
        _ => false
    };
    private static void AddStack(AbiShape shape, List<AbiPiece> pieces, ref int stack)
    {
        stack = Align(stack, Math.Max(8, shape.Alignment));
        pieces.Add(new(new StackLocation(stack), 0, shape.Size));
        stack = checked(stack + Align(shape.Size, 8));
    }
    private static AbiValue Return(AbiShape shape)
    {
        if (shape.Kind == ShapeKind.Void) return new(shape, new([]));
        if (shape.Kind == ShapeKind.Composite && shape.Size > 16)
            return new(shape, Sequence<AbiPiece>.Of(new AbiPiece(new RegisterLocation("X8"), 0, 8)), true);
        if (shape.Kind is ShapeKind.Float or ShapeKind.HomogeneousFloat)
        {
            var count = shape.Kind == ShapeKind.Float ? 1 : shape.ElementCount;
            var size = shape.Kind == ShapeKind.Float ? shape.Size : shape.ElementSize;
            return new(shape, new(Enumerable.Range(0, count).Select(i => new AbiPiece(new RegisterLocation($"V{i}"), i * size, size))));
        }
        return new(shape, new(Enumerable.Range(0, (shape.Size + 7) / 8).Select(i =>
            new AbiPiece(new RegisterLocation($"X{i}"), i * 8, Math.Min(8, shape.Size - i * 8)))));
    }
    private static int Align(int value, int alignment) => checked((value + alignment - 1) / alignment * alignment);
}
