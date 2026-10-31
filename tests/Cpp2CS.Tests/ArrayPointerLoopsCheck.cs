using Cpp2CS.Idioms;
using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;

namespace Cpp2CS.Tests;

internal static class ArrayPointerLoopsCheck
{
    [Command("array-pointer-loops", "数组指针步进与数组类型、元素宽度边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "byte", "float", "reference", "field", "unknown", "mismatch" })
        {
            var width = mode == "byte" ? 1 : mode == "reference" ? 8 : mode == "field" ? 104 : 4;
            var array = new Variable(Storage.Gpr(0), 0);
            var origin = new Variable(Storage.Gpr(1), 1);
            var pointer = new Variable(Storage.Gpr(1), 2);
            var next = new Variable(Storage.Gpr(1), 3);
            Expr U(Variable v) => new Use(v, 64);
            var entry = new Block(0) { End = 16, Statements = [new Define(0, origin, new Binary(BinOp.Add, U(array), Expr.C(32, 64), 64)), new Jump(4, 16)] };
            var loop = new Block(16) { End = 32, Statements = [new Phi(16, pointer, [origin, next]), new Store(20, U(pointer), Expr.C(0, mode == "field" ? 8 : width * 8)),
                new Define(24, next, new Binary(BinOp.Add, U(pointer), Expr.C((ulong)(mode == "mismatch" ? 8 : width), 64), 64)), new Branch(28, Expr.C(1, 1), 16, 32)] };
            var done = new Block(32) { End = 36, Statements = [new Return(32)] };
            MachineFunction.AddEdge(entry, loop); MachineFunction.AddEdge(loop, loop); MachineFunction.AddEdge(loop, done);
            if (mode == "field")
            {
                entry.Statements[0] = new Define(0, origin, new Binary(BinOp.Add, U(array), Expr.C(123, 64), 64));
                loop.Statements[1] = new Store(20, U(pointer), Expr.C(0, 8));
            }
            var function = new MachineFunction { Entry = 0, Range = new(0, 36, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, loop, done] };
            var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
            var serial = 0;
            function.Renumber();
            var changed = ArrayPointerLoopsPass.Run(function, mode == "unknown" ? new Dictionary<Variable, int>() : new() { [array] = width },
                e => e is Use u ? definitions.GetValueOrDefault(u.Variable) : null, () => new Variable(Storage.Temp(serial++), 1));
            a.Equal(mode is "byte" or "float" or "reference" or "field", changed, mode);
            if (!changed) continue;
            var index = loop.Statements.OfType<Phi>().Single();
            a.True(index.Target != pointer && index.Sources.Length == 2, "以独立整数索引保存循环进度");
            var address = loop.Statements.OfType<Store>().Single().Target;
            a.True(ExprMap.Walk(address).Contains(U(array)) && !ExprMap.Walk(address).Contains(U(pointer)), "访存使用原数组及索引，消除指针合流");
            a.True(entry.Statements.Last() is Jump && loop.Statements.Last() is Branch, "入口和循环分支位置不变");
        }
        return a.Finish("array-pointer-loops");
    }
}
