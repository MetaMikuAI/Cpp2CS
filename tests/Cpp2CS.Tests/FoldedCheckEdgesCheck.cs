using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class FoldedCheckEdgesCheck
{
    [Command("folded-check-edges", "条件抛出折叠的落地点与异常状态输入", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var first = new Variable(Storage.Gpr(19), 1); var second = new Variable(Storage.Gpr(19), 2);
        var merged = new Variable(Storage.Gpr(19), 3); var constant = new Variable(Storage.Gpr(20), 1);
        var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 16, 32)] };
        Block Head(ulong address, Variable value, ulong bits) => new(address) { Statements = [new Define(address, value, Expr.C(bits, 64)),
            new Branch(address + 4, Expr.C(1, 1), 48, 64)] };
        var left = Head(16, first, 42); var right = Head(32, second, 17);
        var thrown = new Block(48) { Statements = [new Phi(48, merged, [first, second]), new Define(48, constant, Expr.C(7, 64)),
            new Call(52, CallKind.Direct, Expr.C(256, 64))] };
        var exit = new Block(64) { Statements = [new Return(64)] };
        var handler = new Block(80) { IsLandingPad = true, Statements = [new Return(80)
            { Value = new Binary(BinOp.Add, new Use(merged, 64), new Use(constant, 64), 64) }] };
        MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
        MachineFunction.AddEdge(left, thrown); MachineFunction.AddEdge(left, exit);
        MachineFunction.AddEdge(right, thrown); MachineFunction.AddEdge(right, exit);
        MachineFunction.AddEdge(thrown, handler); thrown.Handler = handler;
        var function = new MachineFunction { Entry = 0, Range = new(0, 96, CodeRegion.Managed, BoundaryEvidence.EhFrame),
            Blocks = [entry, left, right, thrown, exit, handler] };
        function.Renumber();
        var next = 0;
        foreach (var head in new[] { left, right })
        {
            a.True(FoldedCheckEdges.Preserve(function, head, thrown, 0, () => new(Storage.Temp(next++), 1)), "保留异常去向");
            head.Statements[^1] = new Call(head.Start + 4, CallKind.Direct, Expr.C(256, 64))
                { Op = new(OpKind.ThrowIf, "System.Exception"), Arguments = [Expr.C(1, 1)], NativeExceptionSite = 52 };
            head.Statements.Add(new Jump(head.Start + 4, exit.Start));
            MachineFunction.RemoveEdgeAt(head, 0);
        }
        function.Renumber();
        a.True(!function.Blocks.Contains(thrown) && function.Blocks.Contains(handler), "旧抛出块删除后落地点仍可达");
        a.True(handler.Predecessors.SequenceEqual([left, right]) && handler.Statements.OfType<Phi>().Count() == 2,
            "两个折叠检查分别携带状态和常量");
        var returned = (Binary)((Return)handler.Statements[^1]).Value!;
        foreach (var (head, expected) in new[] { (left, 49UL), (right, 24UL) })
        {
            var values = head.Statements.OfType<Define>().ToDictionary(d => d.Target, d => ((Const)d.Value).Value);
            var index = handler.Predecessors.IndexOf(head);
            foreach (var phi in handler.Statements.OfType<Phi>()) values[phi.Target] = values[phi.Sources[index]];
            a.Equal(expected, values[((Use)returned.Left).Variable] + values[((Use)returned.Right).Variable], "异常路径保留各自输入");
        }
        return a.Finish("folded-check-edges");
    }
}
