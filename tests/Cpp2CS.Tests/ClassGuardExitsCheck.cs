using Cpp2CS.Machine.Flow;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class ClassGuardExitsCheck
{
    [Command("class-guard-exits", "类初始化出口的跳转、异常和汇合值边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "direct", "bridge", "effect", "cycle", "handler", "same-phi", "different-phi", "different-exit" })
        {
            var left = new Block(0x100); var right = new Block(0x200);
            var bridge = new Block(0x300) { Statements = [new Jump(0x300, 0x400)] };
            var exit = new Block(0x400) { Statements = [new Return(0x400)] };
            var other = new Block(0x500) { Statements = [new Return(0x500)] };
            MachineFunction.AddEdge(left, exit);
            MachineFunction.AddEdge(right, mode == "direct" ? exit : bridge);
            MachineFunction.AddEdge(bridge, mode == "different-exit" ? other : exit);
            if (mode == "different-exit") bridge.Statements[0] = new Jump(0x300, other.Start);
            if (mode == "effect") bridge.Statements.Insert(0, new Store(0x300, Expr.C(0, 64), Expr.C(1, 64)));
            if (mode == "handler") bridge.Handler = other;
            if (mode == "cycle")
            {
                MachineFunction.RemoveEdge(bridge, exit); MachineFunction.AddEdge(bridge, bridge);
                bridge.Statements[0] = new Jump(0x300, bridge.Start);
            }
            if (mode is "same-phi" or "different-phi")
            {
                var source = new Variable(Storage.Gpr(0), 1);
                exit.Statements.Insert(0, new Phi(exit.Start, source with { Version = 3 }, [source, mode == "same-phi" ? source : source with { Version = 2 }]));
            }
            a.Equal(mode is "direct" or "bridge" or "same-phi", ClassGuardExits.Same(left, exit.Start, right, mode == "direct" ? exit.Start : bridge.Start), $"{mode} 的出口一致性");
            if (mode == "different-phi")
            {
                a.True(ClassGuardExits.Same(left, exit.Start, right, bridge.Start, (x, y) => x.Storage == y.Storage), "允许调用者证明两臂同值");
                a.Equal(false, ClassGuardExits.Same(left, exit.Start, right, bridge.Start, (x, y) => false), "拒绝不同业务值");
            }
        }
        return a.Finish("class-guard-exits");
    }
}
