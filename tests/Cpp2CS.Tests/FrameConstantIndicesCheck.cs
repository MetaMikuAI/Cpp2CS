using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameConstantIndicesCheck
{
    [Command("frame-constant-indices", "帧下标的到达常量、快照与别名拒绝边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "same", "snapshot", "different", "partial", "call-escape", "store-escape", "unknown-alias", "uninitialized" })
        {
            var counter = new FrameAddress(-32);
            var index = new Variable(Storage.Gpr(8), 1);
            var input = new Use(new Variable(Storage.Gpr(0), 0), 64);
            var entry = new Block(0x100);
            var left = new Block(0x110);
            var right = new Block(0x120);
            var join = new Block(0x130);
            if (mode != "uninitialized") entry.Statements.Add(new Store(0x100, counter, Expr.C(0, 32)));
            entry.Statements.Add(new Branch(0x104, new Compare(Cond.Eq, input, Expr.C(0, 64)), left.Start, right.Start));
            left.Statements.Add(new Jump(0x110, join.Start));
            if (mode == "different") right.Statements.Add(new Store(0x120, counter, Expr.C(1, 32)));
            if (mode == "partial") right.Statements.Add(new Store(0x120, new FrameAddress(-30), Expr.C(0, 16)));
            if (mode == "call-escape") right.Statements.Add(new Call(0x120, CallKind.Direct, Expr.C(0x500, 64)) { Arguments = [counter] });
            if (mode == "store-escape") right.Statements.Add(new Store(0x120, input, counter));
            right.Statements.Add(new Jump(0x124, join.Start));
            if (mode == "unknown-alias") join.Statements.Add(new Store(0x130, new Binary(BinOp.Add, new FrameAddress(-64), input, 64), Expr.C(9, 32)));
            join.Statements.Add(new Define(0x134, index, new Load(counter, 32)));
            if (mode == "snapshot") join.Statements.Add(new Store(0x138, counter, Expr.C(1, 32)));
            join.Statements.Add(new Store(0x13c, new Binary(BinOp.Add, new FrameAddress(-64),
                new Binary(BinOp.Shl, new Ir.Convert(ConvKind.SignExtend, new Use(index, 32), 64), Expr.C(3, 64), 64), 64), input));
            join.Statements.Add(new Return(0x140));
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, join); MachineFunction.AddEdge(right, join);
            var function = new MachineFunction { Entry = entry.Start, Range = new(entry.Start, 0x144, CodeRegion.Managed, default), Blocks = [entry, left, right, join] };
            var changed = FrameConstantIndices.Run(function);
            a.Equal(mode is "same" or "snapshot" ? 1 : 0, changed, mode);
            if (changed != 0) a.Equal(new FrameAddress(-64), ((Store)join.Statements[^2]).Target, "使用读取时快照，保留实际栈写入");
        }
        return a.Finish("frame-constant-indices");
    }
}
