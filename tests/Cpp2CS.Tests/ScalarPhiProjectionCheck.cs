using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ScalarPhiProjectionCheck
{
    [Command("scalar-phi-projection", "只读低位的合流快照与完整来源保留", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var wide in new[] { false, true })
        {
            var input = new Variable(Storage.Gpr(0), 0);
            var other = new Variable(Storage.Gpr(1), 0);
            var merged = new Variable(Storage.Gpr(2), 1);
            var masked = new Variable(Storage.Gpr(3), 1);
            var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 4, 8)] };
            var left = new Block(4) { Statements = [new Store(4, Expr.C(1024, 64), new Use(input, 64)), new Jump(4, 12)] };
            var right = new Block(8) { Statements = [new Jump(8, 12)] };
            var join = new Block(12) { Statements = [new Phi(12, merged, [input, other]),
                new Define(16, masked, new Binary(BinOp.And, new Use(merged, 64), Expr.C(uint.MaxValue, 64), 64)),
                new Return(20) { Value = new Use(wide ? merged : masked, wide ? 64 : 32) }] };
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, join); MachineFunction.AddEdge(right, join);
            var function = new MachineFunction { Entry = 0, Range = new(0, 24, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, left, right, join] };
            a.Equal(wide ? 0 : 1, ScalarPhiProjection.Run(function), "仅低位观察可收窄，完整读取不收窄");
            a.True(left.Statements.OfType<Store>().Single().Value is Use { Width: 64 }, "来源的独立完整读取不改变");
            if (!wide)
                a.True(left.Statements is [Store, Define { Value: Use { Width: 32 } }, Jump]
                    && right.Statements is [Define { Value: Use { Width: 32 } }, Jump]
                    && join.Statements.OfType<Phi>().Single().Sources.SequenceEqual(
                        [left.Statements.OfType<Define>().Single().Target, right.Statements.OfType<Define>().Single().Target]),
                    "窄快照位于对应入边且保持来源顺序");
        }
        return a.Finish("scalar-phi-projection");
    }
}
