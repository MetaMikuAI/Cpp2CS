using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ArrayCursorCheck
{
    [Command("array-cursors", "数组指针与循环下标的成对归纳", Gate = Gate.Unit)]
    public static int Run()
    {
        var array = new Variable(Storage.Gpr(0), 0);
        var pointer = new Variable(Storage.Gpr(1), 2);
        var counter = new Variable(Storage.Gpr(2), 2);
        Expr Add(Variable value, long amount) => new Binary(BinOp.Add, new Use(value, 64), Expr.C(unchecked((ulong)amount), 64), 64);
        MachineFunction Loop(long first = 4, long stride = 16, long increment = 1, bool swap = false, bool earlyRoot = true)
        {
            var p0 = pointer with { Version = 1 };
            var p1 = pointer with { Version = 3 };
            var i0 = counter with { Version = 1 };
            var i1 = counter with { Version = 3 };
            var root = earlyRoot ? array : array with { Version = 1 };
            var entry = new Block(0x1000) { Statements = [new Define(0x1000, p0, Add(root, 32)), new Define(0x1004, i0, Expr.C(unchecked((ulong)first), 64))] };
            var loop = new Block(0x1010) { Statements = [new Phi(0x1010, pointer, [p0, p1]), new Phi(0x1010, counter, swap ? [i1, i0] : [i0, i1]),
                new Define(0x1014, p1, Add(pointer, stride)), new Define(0x1018, i1, Add(counter, increment))] };
            if (!earlyRoot) loop.Statements.Add(new Define(0x101c, root, new Use(array, 64)));
            MachineFunction.AddEdge(entry, loop);
            MachineFunction.AddEdge(loop, loop);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1020, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, loop] };
            function.Renumber();
            return function;
        }
        ArrayCursorRecognition.Cursor[] Read(MachineFunction f) => ArrayCursorRecognition.Read(f, e => e is Use u && u.Variable.Storage == array.Storage ? 16 : null).ToArray();
        var a = new Assertions();
        var sample = Read(Loop());
        a.Equal(1, sample.Length, "指针与下标同循环递增");
        a.Equal(pointer, sample.Single().Pointer, "归纳目标为元素指针");
        a.True(sample.Single().Address is Binary { Left: Binary { Right: Const bias }, Right: Binary { Right: Const scale } }
            && bias.Signed == -32 && scale.Value == 16, "初始下标包含数组头时保留负偏移");
        a.Equal(2, sample.Single().AddressCopies.Count, "仅消去指针初值和递增副本");
        a.Equal(1, Read(Loop(first: 0, stride: 32, increment: 2)).Length, "允许同倍数递增");
        a.Equal(1, Read(Loop(first: 6, stride: -16, increment: -1)).Length, "允许对应的反向遍历");
        a.Equal(0, Read(Loop(stride: 8)).Length, "步长必须匹配元素大小");
        a.Equal(0, Read(Loop(increment: 0)).Length, "指针变化而下标不变时拒绝");
        a.Equal(0, Read(Loop(swap: true)).Length, "前驱边必须一一对应");
        a.Equal(0, Read(Loop(earlyRoot: false)).Length, "循环内重建的数组不能当作固定根");
        return a.Finish("array-cursors");
    }
}
