using Cpp2CS.Facts;
using Cpp2CS.Input;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameTypedProjectionCheck
{
    [Command("frame-typed-projection", "已定型栈结构体的部分寄存器投影边界", Arguments = "<binary> <metadata>", Gate = Gate.Image)]
    public static int Run(string binary, string metadata)
    {
        var facts = FactsBuilder.Build(binary, metadata, inferUnregistered: false);
        var types = new ManagedTypes(facts.Model, facts.Layouts);
        DefinitionRef Type(string name) => new(facts.Model.Types.Single(t => t.FullName == name), []);
        var vector2 = Type("UnityEngine.Vector2");
        var vector3 = Type("UnityEngine.Vector3");
        var vector2Int = Type("UnityEngine.Vector2Int");
        var method = types.CorlibMethod("System.Object", "MemberwiseClone")!;
        var ctx = new RecoveryScope(new MethodRecovery(facts, types), method, 0x100);
        var write = new Call(0x100, CallKind.Direct, Expr.C(0, 64));
        var read = new Define(0x104, new Variable(Storage.Vec(0), 1), new Load(new FrameAddress(-36), 32));
        var block = new Block(0x100) { Statements = [write, read] };
        ctx.blocks = [block];
        List<FrameWitness> witnesses = [new(-40, vector2, write, true)];
        var a = new Assertions();
        a.True(ctx.TypedFrameRead(witnesses, -40, vector3, [read], [(4, 32, -36)]), "Vector2.y 可作为 Vector3.y，不扩大源区域");
        a.True(!ctx.TypedFrameRead(witnesses, -40, vector3, [read]), "完整 Vector3 读取仍超出 Vector2");
        a.True(!ctx.TypedFrameRead(witnesses, -40, vector3, [read], [(8, 32, -32)]), "实际读取越界仍拒绝");
        a.True(!ctx.TypedFrameRead(witnesses, -40, vector2Int, [read], [(4, 32, -36)]), "同宽但字段类型不同仍拒绝");
        a.True(ctx.TypedFrameRead(witnesses, -40, vector2, [read]), "原有完整同型读取继续接受");
        block.Statements = [read, write];
        a.True(!ctx.TypedFrameRead(witnesses, -40, vector3, [read], [(4, 32, -36)]), "读取之后的写入不能提供类型证据");
        var firstValue = new Variable(Storage.Gpr(1), 1);
        var otherValue = new Variable(Storage.Gpr(2), 1);
        var entry = new Block(0x200) { Statements = [new Branch(0x200, Expr.C(1, 1), 0x210, 0x230)] };
        var firstCall = new Call(0x218, CallKind.Direct, Expr.C(0, 64));
        var first = new Block(0x210) { Statements = [new Define(0x210, firstValue, new Load(new FrameAddress(-64), 64)),
            new Store(0x214, new FrameAddress(-16), new Use(firstValue, 64)), firstCall, new Return(0x21c)] };
        var other = new Block(0x230) { Statements = [new Define(0x230, otherValue, new Load(new FrameAddress(-96), 64)),
            new Store(0x234, new FrameAddress(-16), new Use(otherValue, 64)), new Return(0x238)] };
        MachineFunction.AddEdge(entry, first);
        MachineFunction.AddEdge(entry, other);
        ctx.function = new() { Entry = entry.Start, Range = new(0x200, 0x240, CodeRegion.Managed, default), Blocks = [entry, first, other] };
        ctx.function.Renumber();
        ctx.blocks = ctx.function.Blocks;
        ctx.definitions = ctx.IndexDefinitions();
        var copied = new List<FrameWitness> { new(-16, vector2, firstCall, false) };
        ctx.WitnessFrameCopies(copied);
        a.True(copied.Any(w => w.Offset == -64 && w.Type.Equals(vector2)), "复制类型沿到达调用的路径回传");
        a.True(copied.All(w => w.Offset != -96), "同一目标槽不能把类型回传到互斥分支的来源");
        var array = new Variable(Storage.Gpr(8), 1);
        var cursor = new Variable(Storage.Gpr(9), 1);
        first.Statements.Insert(0, new Define(0x20c, cursor, new Binary(BinOp.Add, new Use(array, 64), new Use(new(Storage.Gpr(10), 1), 64), 64)));
        ctx.definitions = ctx.IndexDefinitions();
        a.True(!ctx.FieldAddress(cursor), "未知基址不作为可分离的数组地址");
        ctx.State.Types.known[array] = new ArrayRef(types.Byte, 1) { IsVector = true };
        a.True(ctx.FieldAddress(cursor), "已知字节数组的偏移地址可按合流入边分离");
        var vector = new Variable(Storage.Vec(4), 1);
        var low = new ArgumentValue(0, types.String, 64);
        var high = new ArgumentValue(1, types.UInt64, 64);
        ctx.State.Structs.fragmentLocals[vector] = new Fragment([new Part(0, low), new Part(64, high)], types.UInt64, 128);
        var value = new Use(vector, 128);
        var left = new Binary(BinOp.LShr, value, Expr.C(64, 128), 128);
        var right = new Binary(BinOp.Shl, value, Expr.C(64, 128), 128);
        foreach (var expression in new[] { new Binary(BinOp.Or, left, right, 128), new Binary(BinOp.Or, right, left, 128) })
        {
            a.True(ctx.Binary(expression).TryGet(out var swapped, out _), "半段互换不要求 128 位整数常量类型");
            a.True(swapped is Fragment { Parts: [var firstPart, var lastPart] }
                && firstPart.Low == 0 && firstPart.Value == high && lastPart.Low == 64 && lastPart.Value == low, "互换保持引用叶子和整数叶子的身份");
        }
        a.True(ctx.Binary(new Binary(BinOp.Or, left with { Right = Expr.C(32, 128) }, right, 128)).Failure is not null,
            "移位不互补时不能按半段互换恢复");
        return a.Finish("frame-typed-projection");
    }
}
