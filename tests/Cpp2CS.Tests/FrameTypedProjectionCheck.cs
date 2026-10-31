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
        return a.Finish("frame-typed-projection");
    }
}
