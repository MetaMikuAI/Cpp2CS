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
        a.True(!sample.Single().IsOffset, "含数组根的指针不能作为普通整数展开");
        a.True(sample.Single().Address is Binary { Left: Binary { Right: Const bias }, Right: Binary { Right: Const scale } }
            && bias.Signed == -32 && scale.Value == 16, "初始下标包含数组头时保留负偏移");
        a.Equal(2, sample.Single().AddressCopies.Count, "仅消去指针初值和递增副本");
        a.Equal(1, Read(Loop(first: 0, stride: 32, increment: 2)).Length, "允许同倍数递增");
        a.Equal(1, Read(Loop(first: 6, stride: -16, increment: -1)).Length, "允许对应的反向遍历");
        a.Equal(0, Read(Loop(stride: 8)).Length, "步长必须匹配元素大小");
        a.Equal(0, Read(Loop(increment: 0)).Length, "指针变化而下标不变时拒绝");
        a.Equal(0, Read(Loop(swap: true)).Length, "前驱边必须一一对应");
        a.Equal(0, Read(Loop(earlyRoot: false)).Length, "循环内重建的数组不能当作固定根");
        MachineFunction OffsetLoop(bool scalarUse = false, bool copyEscapes = false, long stride = 16)
        {
            var function = Loop(first: 0, stride: stride);
            var initial = (Define)function.Blocks[0].Statements[0];
            function.Blocks[0].Statements[0] = initial with { Value = Expr.C(32, 64) };
            function.Blocks[1].Statements.Add(new Define(0x101c, new Variable(Storage.Gpr(3), 1),
                new Binary(BinOp.Add, new Use(array, 64), new Use(pointer, 64), 64)));
            if (scalarUse) function.Blocks[1].Statements.Add(new Return(0x1020) { Value = new Use(pointer, 64) });
            if (copyEscapes) function.Blocks[1].Statements.Add(new Return(0x1020) { Value = new Use(initial.Target, 64) });
            return function;
        }
        var offset = Read(OffsetLoop());
        a.Equal(1, offset.Length, "字节偏移与元素下标成对递增");
        a.True(offset.Single().IsOffset, "纯字节偏移可还原数值用途");
        a.True(offset.Single().Address is Binary { Left: Binary { Left: Const { Value: 0 }, Right: Const { Value: 32 } } }, "保留数组头偏移");
        a.Equal(1, Read(OffsetLoop(scalarUse: true)).Length, "偏移作为普通数值返回时保留归纳关系");
        a.Equal(1, Read(OffsetLoop(copyEscapes: true)).Length, "初值副本的数值用途由副本表达式保留");
        foreach (var index in new[] { 0UL, 1UL, 7UL, ulong.MaxValue })
        {
            var evaluator = new Evaluator();
            evaluator.Registers[counter.Storage] = index;
            var expression = ExprMap.Map(offset.Single().Address, e => e is Use use ? new Read(use.Variable.Storage, use.Width) : null);
            a.Equal<UInt128>(unchecked(32 + index * 16), evaluator.Eval(expression), "偏移关系保留 64 位回绕");
        }
        a.Equal(0, Read(OffsetLoop(stride: 8)).Length, "字节步长不符时拒绝");
        MachineFunction NarrowLoop(Cond comparison = Cond.Slt, bool bypass = false, ulong initialIndex = 0, ulong increment = 1)
        {
            var function = OffsetLoop();
            var entry = function.Blocks[0];
            entry.Statements[1] = new Define(0x1004, counter with { Version = 1 }, Expr.C(initialIndex, 64));
            var loop = function.Blocks[1];
            var advance = new Block(0x1030) { Statements = loop.Statements.OfType<Define>().ToList<Stmt>() };
            var indexStep = advance.Statements.OfType<Define>().Single(d => d.Target == (counter with { Version = 3 }));
            advance.Statements[advance.Statements.IndexOf(indexStep)] = indexStep with { Value = new Ir.Convert(ConvKind.ZeroExtend,
                new Binary(BinOp.Add, new Use(counter, 32), Expr.C(increment, 32), 32), 64) };
            loop.Statements.RemoveAll(s => s is Define);
            var done = new Block(0x1040) { Statements = [new Return(0x1040)] };
            loop.Statements.Add(new Branch(0x1020, new Compare(comparison, new Use(counter, 32), Expr.C(int.MaxValue, 32)), advance.Start, done.Start));
            loop.Successors.Remove(loop);
            loop.Predecessors.Remove(loop);
            MachineFunction.AddEdge(loop, advance);
            MachineFunction.AddEdge(loop, done);
            MachineFunction.AddEdge(advance, loop);
            if (bypass) MachineFunction.AddEdge(entry, advance);
            function.Blocks.AddRange([advance, done]);
            function.Renumber();
            return function;
        }
        a.Equal(1, Read(NarrowLoop()).Length, "有严格有符号上界的 32 位下标不会回绕");
        a.Equal(0, Read(NarrowLoop(comparison: Cond.Ult)).Length, "无符号上界可能包含 int.MaxValue 以外的值");
        a.Equal(0, Read(NarrowLoop(comparison: Cond.Sle)).Length, "包含上界时加一可能越过 int.MaxValue");
        a.Equal(0, Read(NarrowLoop(bypass: true)).Length, "递增不能绕过边界分支");
        a.Equal(0, Read(NarrowLoop(initialIndex: uint.MaxValue)).Length, "拒绝 32 位负数种子");
        a.Equal(0, Read(NarrowLoop(increment: 2)).Length, "窄下标暂只接受有界逐次加一");
        var firstIndex = new Variable(Storage.Gpr(4), 0);
        MachineFunction IndexedLoop(bool sameIndex = true, bool arrayBound = true, bool bypass = false)
        {
            var function = NarrowLoop(bypass: bypass);
            var entry = function.Blocks[0];
            Expr index = new Ir.Convert(ConvKind.SignExtend, new Use(firstIndex, 32), 64);
            var scaled = new Binary(BinOp.Mul, index, Expr.C(16, 64), 64);
            entry.Statements[0] = new Define(0x1000, pointer with { Version = 1 }, new Binary(BinOp.Add,
                new Binary(BinOp.Add, new Use(array, 64), scaled, 64), Expr.C(32, 64), 64));
            entry.Statements[1] = new Define(0x1004, counter with { Version = 1 }, new Ir.Convert(ConvKind.ZeroExtend,
                new Use(sameIndex ? firstIndex : firstIndex with { Storage = Storage.Gpr(5) }, 32), 64));
            var loop = function.Blocks[1];
            loop.Statements.RemoveAll(s => s is Branch);
            Expr length = arrayBound ? new Load(Add(array, RuntimeLayout.ArrayMaxLength), 32) : new Use(new(Storage.Gpr(6), 0), 32);
            loop.Statements.Add(new Call(0x1020, CallKind.Direct, Expr.C(0, 64))
                { Op = new(OpKind.BoundsCheck, null), Arguments = [new Use(counter, 32), length] });
            loop.Statements.Add(new Jump(0x1024, 0x1030));
            var done = function.Blocks.Single(b => b.Start == 0x1040);
            loop.Successors.Remove(done);
            done.Predecessors.Remove(loop);
            function.Blocks.Remove(done);
            function.Renumber();
            return function;
        }
        var indexed = Read(IndexedLoop());
        a.Equal(1, indexed.Length, "动态有符号起点与零扩展的循环下标可按低位对应");
        a.Equal(0, Read(IndexedLoop(sameIndex: false)).Length, "指针与下标起点不同时拒绝");
        a.Equal(0, Read(IndexedLoop(arrayBound: false)).Length, "未知长度的无符号边界检查不证明有符号递增无溢出");
        a.Equal(0, Read(IndexedLoop(bypass: true)).Length, "不能绕过数组边界检查执行递增");
        foreach (var index in new[] { -2, -1, 0, 1, 8, int.MaxValue })
        {
            var evaluator = new Evaluator();
            evaluator.Registers[array.Storage] = 0x10000;
            evaluator.Registers[counter.Storage] = unchecked((uint)index);
            var expression = ExprMap.Map(indexed.Single().Address, e => e is Use use ? new Read(use.Variable.Storage, use.Width) : null);
            a.Equal<UInt128>(unchecked((ulong)(0x10000L + 32 + (long)index * 16)), evaluator.Eval(expression), "动态起点保留符号；负下标仍交由原边界检查抛出");
        }
        return a.Finish("array-cursors");
    }
}
