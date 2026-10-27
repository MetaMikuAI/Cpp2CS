using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

internal static class FrameExtentCheck
{
    [Command("frame-extents", "有界 ref 参数与相邻标量栈槽", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        MachineFunction Function(long scalar, int width = 32, bool storedAddress = false)
        {
            var block = new Block(0x1000) { Statements = [
                new Store(0x1000, new FrameAddress(scalar), Expr.C(7, width)),
                new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64)) { Arguments = [new FrameAddress(-64)], Sources = [Storage.Gpr(0)] },
                new Return(0x1008) { Value = new Load(new FrameAddress(scalar), width) }] };
            if (storedAddress) block.Statements.Insert(1, new Store(0x1002, Expr.C(0x3000, 64), new FrameAddress(-64)));
            return new() { Entry = block.Start, Range = new(0x1000, 0x1010, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
        }
        a.Equal(0, FrameSlotPromotion.Run(Function(-40)), "无边界的指针仍保护其上方栈槽");
        a.Equal(1, FrameSlotPromotion.Run(Function(-40), (_, _) => 16), "ref 结构后独立标量可提升");
        a.Equal(1, FrameSlotPromotion.Run(Function(-48), (_, _) => 16), "紧邻结构末尾的槽不重叠");
        a.Equal(0, FrameSlotPromotion.Run(Function(-52), (_, _) => 16), "结构末尾内部不能提升");
        a.Equal(0, FrameSlotPromotion.Run(Function(-68, 64), (_, _) => 16), "从下方跨入结构的访问不能提升");
        a.Equal(1, FrameSlotPromotion.Run(Function(-72), (_, _) => 16), "结构下方独立标量可提升");
        a.Equal(0, FrameSlotPromotion.Run(Function(-40, storedAddress: true), (_, _) => 16), "其他位置仍逃逸时不能由单个有界调用解除限制");
        a.Equal(0, FrameSlotPromotion.Run(Function(-40), (_, _) => 16, [(-40, 16)]), "结构体返回值的分片仍保留为完整帧区域");
        var promoted = Function(-40);
        FrameSlotPromotion.Run(promoted, (_, _) => 16);
        a.True(promoted.Blocks[0].Statements[0] is Assign && promoted.Blocks[0].Statements[2] is Return { Value: Read }, "成对替换标量写入与读取");
        foreach (var outward in new[] { false, true })
        {
            var block = new Block(0x1000);
            var root = new Use(new Variable(Storage.Gpr(0), 0), 64);
            foreach (var (offset, width) in new[] { (0, 128), (16, 128), (32, 64) })
            {
                var variable = new Variable(width == 128 ? Storage.Vec(offset / 16) : Storage.Gpr(1), 1);
                Expr frame = new FrameAddress(-64 + offset);
                Expr external = new Binary(BinOp.Add, root, Expr.C((ulong)offset, 64), 64);
                block.Statements.Add(new Define((ulong)(0x1000 + offset), variable, new Load(outward ? frame : external, width)));
                block.Statements.Add(new Store((ulong)(0x1004 + offset), outward ? external : frame, new Use(variable, width)));
            }
            var function = new MachineFunction { Entry = block.Start, Range = new(0x1000, 0x1040, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
            a.True(FrameCopySpans.Read(function).SequenceEqual(new[] { (-64L, 40) }), "连续宽复制保留两侧标量尾部");
            block.Statements.Add(new Store(0x1030, new FrameAddress(-16), Expr.C(1, 64)));
            block.Statements.Add(new Return(0x1034) { Value = new Load(new FrameAddress(-16), 64) });
            a.Equal(1, FrameSlotPromotion.Run(function, preserved: FrameCopySpans.Read(function).ToArray()), "范围以外的独立标量仍可提升");
        }
        return a.Finish("frame-extents");
    }
}
