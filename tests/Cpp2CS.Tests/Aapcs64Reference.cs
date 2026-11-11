using Cpp2CS.Native;
using Cpp2CS.Native.Abi;
using Cpp2CS.Targets.Arm64.Abi;

namespace Cpp2CS.Tests;

/// <summary>迁自独立 Aapcs64Classifier 的 Shape/Allocate/Result；不调用产品分类内部函数。</summary>
internal static class Aapcs64Reference
{
    internal enum Kind { Void, Integer, Pointer, Float, Aggregate }
    internal sealed record Shape(Kind Kind, int Size, int Alignment, int FloatWidth = 0, int[]? HfaOffsets = null);
    internal sealed record Piece(AbstractSlot Slot, int Width, int Offset);
    internal sealed record Location(Shape Shape, bool Indirect, Piece[] Pieces, int? StackOffset = null);
    internal sealed class Cursor { public int Gpr; public int Vector; public int Stack; }

    private static Location? Result(Shape shape)
    {
        if (shape.Kind == Kind.Void) return null;
        var result = Allocate(shape, new Cursor());
        return result.Indirect ? new(shape, true, [new(new(SlotKind.IndirectResult), 64, 0)]) : result;
    }

    private static Location Allocate(Shape shape, Cursor state)
    {
        if (shape.Size == 0) return new(shape, false, []);
        var hfa = shape.HfaOffsets;
        if (shape.Kind == Kind.Float || hfa is { Length: > 0 })
        {
            var offsets = hfa ?? [0];
            if (state.Vector + offsets.Length <= 8)
                return new(shape, false, offsets.Select(o => new Piece(new(SlotKind.Floating,state.Vector++), shape.FloatWidth, o)).ToArray());
            state.Vector = 8;
            return OnStack(shape, false, shape.Size, Math.Max(8, shape.Alignment), state);
        }
        var indirect = shape.Kind == Kind.Aggregate && shape.Size > 16;
        var size = indirect ? 8 : shape.Size;
        var alignment = indirect ? 8 : shape.Alignment;
        if (alignment == 16) state.Gpr = Round(state.Gpr, 2);
        var words = (size + 7) / 8;
        if (state.Gpr + words <= 8)
            return new(shape, indirect, Enumerable.Range(0, words)
                .Select(i => new Piece(new(SlotKind.Integer,state.Gpr++), Math.Min(8, size - 8 * i) * 8, 8 * i)).ToArray());
        state.Gpr = 8;
        return OnStack(shape, indirect, size, Math.Max(8, alignment), state);
    }

    private static Location OnStack(Shape shape, bool indirect, int size, int alignment, Cursor state)
    {
        state.Stack = Round(state.Stack, alignment);
        var offset = state.Stack;
        state.Stack += Round(size, 8);
        return new(shape, indirect, [], offset);
    }
    private static int Round(int value, int alignment) => checked((value + alignment - 1) / alignment * alignment);

    public static void Check(Assertions a)
    {
        var random = new Random(1539);
        var catalog = new List<(CType Type, Shape Shape)>();
        foreach (var size in new[] {1,2,4,8,16}) catalog.Add((new CInteger(size*8),new(Kind.Integer,size,size)));
        catalog.Add((new CPointer(64),new(Kind.Pointer,8,8)));
        foreach (var size in new[] {4,8})
        {
            catalog.Add((new CFloat(size*8),new(Kind.Float,size,size,size*8)));
            for (var n = 1; n <= 4; n++)
                catalog.Add((new CAggregate(size*n,size,[new(0,new CArray(new CFloat(size*8),n))]),
                    new(Kind.Aggregate,size*n,size,size*8,Enumerable.Range(0,n).Select(i=>i*size).ToArray())));
        }
        foreach (var size in new[] {0,1,7,8,9,16,24,40})
            catalog.Add((new CAggregate(size,1,size == 0 ? [] : [new(0,new CArray(new CInteger(8),size))]),new(Kind.Aggregate,size,1)));
        catalog.Add((new CAggregate(16,16,[new(0,new CInteger(128))]),new(Kind.Aggregate,16,16)));
        static AbiPiece[] Pieces(Location value) => value.StackOffset is { } stack
            ? [new(0,value.Indirect ? 8 : value.Shape.Size,new(SlotKind.ArgumentArea,stack))]
            : value.Pieces.Select(p=>new AbiPiece(p.Offset,p.Width/8,p.Slot)).ToArray();
        for (var n = 0; n < 10000; n++)
        {
            var args = Enumerable.Range(0,random.Next(25)).Select(_=>catalog[random.Next(catalog.Count)]).ToArray();
            var ret = catalog[random.Next(catalog.Count)];
            var classified = new Aapcs64().Classify(new([..args.Select(t=>t.Type)],ret.Type)).Assignment!;
            var state = new Cursor();
            for (var j = 0; j < args.Length; j++)
            {
                var expected = Allocate(args[j].Shape,state);
                var actual = classified.Parameters[j];
                a.True(expected.Indirect ? actual.CopyAddress == Pieces(expected).Single() && actual.Pieces.Length == 0
                    : actual.CopyAddress is null && actual.Pieces.SequenceEqual(Pieces(expected)),$"独立核对 {n} 参数 {j}");
            }
            var result = Result(ret.Shape)!;
            a.True(result.Indirect ? classified.Return.BufferAddress == Pieces(result).Single()
                : classified.Return.BufferAddress is null && classified.Return.Pieces.SequenceEqual(Pieces(result)),$"独立核对 {n} 返回值");
            a.True(classified.StackSize == Round(state.Stack,16),$"独立核对 {n} 栈大小");
        }
        Console.WriteLine("AAPCS64 独立核对：10000 个随机签名");
    }
}
