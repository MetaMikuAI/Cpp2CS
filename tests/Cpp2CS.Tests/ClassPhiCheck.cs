using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Tests;

internal static class ClassPhiCheck
{
    [Command("class-phis", "相同对象类指针与成对对象合流的身份边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var first = new Variable(Storage.Gpr(0), 0);
        var second = new Variable(Storage.Gpr(1), 0);
        var left = new Variable(Storage.Gpr(2), 1);
        var right = new Variable(Storage.Gpr(2), 2);
        var joined = new Variable(Storage.Gpr(2), 3);
        var receiver = new Variable(Storage.Gpr(3), 1);
        var depthLeft = new Variable(Storage.Gpr(4), 1);
        var depthRight = new Variable(Storage.Gpr(4), 2);
        var depthJoined = new Variable(Storage.Gpr(4), 3);
        Expr Depth(Variable klass) => Fold.Convert(ConvKind.ZeroExtend,
            new Load(new Binary(BinOp.Add, new Use(klass, 64), Expr.C(RuntimeLayout.ClassTypeHierarchyDepth, 64), 64), 8), 64);
        foreach (var same in new[] { true, false })
            foreach (var paired in new[] { true, false })
            {
                var source = same ? first : second;
                var entry = new Block(0) { Statements = [new Branch(0, Expr.C(1, 1), 4, 8)] };
                var one = new Block(4) { Statements = [new Define(4, left, new Load(new Use(first, 64), 64)), new Jump(4, 12)] };
                var two = new Block(8) { Statements = [new Define(8, right, new Load(new Use(source, 64), 64)), new Jump(8, 12)] };
                var merge = new Block(12) { Statements = [new Phi(12, joined, [left, right]), new Return(16)] };
                one.Statements.Insert(1, new Define(4, depthLeft, Depth(left)));
                two.Statements.Insert(1, new Define(8, depthRight, Depth(right)));
                merge.Statements.Insert(1, new Phi(12, depthJoined, [depthLeft, depthRight]));
                if (paired) merge.Statements.Insert(0, new Phi(12, receiver, [first, source]));
                MachineFunction.AddEdge(entry, one); MachineFunction.AddEdge(entry, two);
                MachineFunction.AddEdge(one, merge); MachineFunction.AddEdge(two, merge);
                var function = new MachineFunction { Entry = 0, Range = new(0, 20, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                    Blocks = [entry, one, two, merge] };
                var expanded = new IdiomRewriter.Defs(function).Expand(new Use(joined, 64));
                a.True(same ? expanded == new Load(new Use(first, 64), 64)
                    : paired ? expanded == new Load(new Use(receiver, 64), 64) : expanded == new Use(joined, 64),
                    "只有相同对象或逐边配对的对象合流可以确定类指针");
                var depth = new IdiomRewriter.Defs(function).Expand(new Use(depthJoined, 64));
                a.True(same ? depth is Cpp2CS.Ir.Convert { Operand: Load { Width: 8 } }
                    : depth == new Use(depthJoined, 64), "相同对象的层级长度可合流，不同对象的长度不能混用");
            }
        return a.Finish("class-phis");
    }
}
