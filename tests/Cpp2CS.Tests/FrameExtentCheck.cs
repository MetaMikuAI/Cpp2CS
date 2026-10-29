using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;
using Cpp2CS.Ssa;
using Cpp2CS.Model;
using System.Reflection;

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
        var invocation = new Call(0x1000, CallKind.Indirect, Expr.C(0, 64)) { Arguments = [new FrameAddress(-64)] };
        a.True(FrameUses.Touches(invocation, -32, 16, (_, _) => 48), "结构体传址保留末段写入");
        a.True(!FrameUses.Touches(invocation, -16, 8, (_, _) => 48), "已知长度不覆盖相邻独立槽");
        a.True(FrameUses.Touches(invocation, -16, 8, (_, _) => null), "未知传址范围仍可能读取上方槽");
        a.True(!FrameUses.Touches(new Return(0x1000) { Value = new Load(new FrameAddress(-64), 64) }, -32, 8, (_, _) => null), "精确读取不视为整段逃逸");
        a.True(FrameUses.Touches(new Store(0x1000, Expr.C(0x2000, 64), new FrameAddress(-64)), -32, 8, (_, _) => null), "存入外部内存的地址保护后续分片");
        ManagedBounds(a);
        CallSpills(a);
        return a.Finish("frame-extents");
    }

    private static void CallSpills(Assertions a)
    {
        MachineFunction Sample(bool escape = false, bool overlap = false, long offset = -32)
        {
            var frame = new FrameAddress(offset);
            var block = new Block(0x1000) { Statements = [
                new Store(0x1000, frame, new Use(new(Storage.Vec(0), 1), 128)),
                new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64)),
                new Define(0x1008, new(Storage.Vec(0), 2), new Load(frame, 128))] };
            if (escape) block.Statements.Add(new Define(0x100c, new(Storage.Gpr(1), 1), frame));
            if (overlap) block.Statements.Add(new Store(0x100c, new FrameAddress(-24), Expr.C(1, 32)));
            return new() { Entry = block.Start, Range = new(0x1000, 0x1010, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block] };
        }
        var valid = Sample();
        a.True(FrameSlotPromotion.ForwardCallSpills(valid, _ => true), "已知调用前后的向量保存可回代");
        a.True(valid.Blocks[0].Statements is [Call, Define { Value: Use { Width: 128, Variable.Version: 1 } }], "保留全部 128 位的原 SSA 快照");
        a.True(!FrameSlotPromotion.ForwardCallSpills(Sample(), _ => false), "未知调用不假设无法访问栈");
        a.True(!FrameSlotPromotion.ForwardCallSpills(Sample(escape: true), _ => true), "地址逃逸时保留实际存储");
        a.True(!FrameSlotPromotion.ForwardCallSpills(Sample(overlap: true), _ => true), "部分重叠访问不替换");
        a.True(!FrameSlotPromotion.ForwardCallSpills(Sample(offset: -8), _ => true), "跨入调用者帧的保存不替换");
    }

    private static void ManagedBounds(Assertions a)
    {
        var integer = new TypeDef { Index = 1, Assembly = "mscorlib.dll", Namespace = "System", Name = "Int64", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false };
        var parameter = new GenericParameterDef { Name = "T", Position = 0, Attributes = 0 };
        var packet = new TypeDef { Index = 2, Assembly = "Frame.Tests.dll", Namespace = "Tests", Name = "Packet`1", Token = 0,
            Attributes = TypeAttributes.Public, IsValueType = true, IsEnum = false, GenericParameters = [parameter] };
        packet.Fields = Enumerable.Range(0, 3).Select(i => new FieldDef { Index = i, Owner = packet, Name = "Value" + i,
            Type = new GenericParameterRef("T", false, 0), Offset = -1, Attributes = FieldAttributes.Public }).ToArray();
        var type = new DefinitionRef(packet, [new DefinitionRef(integer, [])]);
        var method = new MethodRef(new MethodDef { Index = 1, Owner = packet, Name = "Copy", Token = 0,
            Attributes = MethodAttributes.Public | MethodAttributes.Static, ImplAttributes = 0, Slot = -1, ReturnType = type,
            Parameters = [new("value", new ByRefRef(type), 0, null, false)] }, type.Arguments, []);
        var call = new Call(0x1000, CallKind.Indirect, Expr.C(0, 64)) { Op = new(OpKind.CallMethodPointer, method),
            Arguments = [new FrameAddress(-64), new FrameAddress(-32)], Sources = [Storage.Gpr(0), Storage.Gpr(8)] };
        var frames = new ManagedCallFrames(null!, new ManagedAbi(new FieldLayouts(null!)));
        a.Equal(24, frames.ArgumentSize(call, 0), "ref 参数的完整结构体长度");
        a.Equal(24, frames.ArgumentSize(call, 1), "x8 返回缓冲区与 ref 参数使用同一布局证明");
        a.True(FrameUses.Touches(call, -16, 8, frames.ArgumentSize), "返回缓冲区尾部必须保留");
        a.True(!FrameUses.Touches(call, -8, 8, frames.ArgumentSize), "返回缓冲区末尾之后的捕获槽不逃逸");
        a.True(frames.ArgumentSize(call with { Sources = [Storage.Gpr(1), Storage.Gpr(8)] }, 0) is null,
            "隐藏元数据参数不能被误认为有界 ref 参数");
    }
}
