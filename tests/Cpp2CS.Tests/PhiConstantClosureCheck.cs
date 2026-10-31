using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Machine.Ssa;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class PhiConstantClosureCheck
{
    [Command("phi-constant-closure", "循环中恢复基址后的常量传播与冲突", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "same", "different", "unknown" })
        {
            Variable V(int index) => new(Storage.Gpr(index), 1);
            var entry = new Block(0) { Statements = [new Define(0, V(1), Expr.C(0x1008, 64)), new Jump(4, 16)] };
            var loop = new Block(16) { Statements = [new Phi(16, V(2), [V(1), V(7)]),
                new Store(20, Expr.C(0x2000, 64), new Use(V(2), 64)), new Branch(24, new Use(V(0), 1), 32, 48)] };
            var left = new Block(32) { Statements = [new Define(32, V(3), Expr.C(0x1000, 64)), new Jump(36, 64)] };
            Expr rightValue = mode == "unknown" ? new Unknown("未证成基址", 64) : Expr.C(mode == "different" ? 0x1100UL : 0x1000UL, 64);
            var right = new Block(48) { Statements = [new Define(48, V(4), rightValue), new Jump(52, 64)] };
            var joined = new Block(64) { Statements = [new Phi(64, V(5), [V(3), V(4)]),
                new Define(68, V(6), new Binary(BinOp.Add, new Use(V(5), 64), Expr.C(8, 64), 64)), new Jump(72, 80)] };
            var back = new Block(80) { Statements = [new Phi(80, V(7), [V(6)]), new Jump(84, 16)] };
            MachineFunction.AddEdge(entry, loop); MachineFunction.AddEdge(loop, left); MachineFunction.AddEdge(loop, right);
            MachineFunction.AddEdge(left, joined); MachineFunction.AddEdge(right, joined); MachineFunction.AddEdge(joined, back); MachineFunction.AddEdge(back, loop);
            var function = new MachineFunction { Entry = 0, Range = new(0, 88, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, loop, left, right, joined, back] };
            function.Renumber();
            Propagate.Run(function, Dominators.Compute(function));
            a.Equal(mode == "same", loop.Statements.OfType<Store>().Single().Value is Const { Value: 0x1008 },
                "循环外初值和各回边重建值必须一致且已证明");
        }
        return a.Finish("phi-constant-closure");
    }
}
