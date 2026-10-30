using System.Reflection;
using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Tests;

internal static class ClassPhiAllocationsCheck
{
    [Command("class-phi-allocations", "类型合流分配的构造、顺序和异常边界", Gate = Gate.Unit)]
    public static int Run()
    {
        DefinitionRef Type(int index) => new(new TypeDef { Index = index, Assembly = "Allocation.Tests.dll", Namespace = "Tests", Name = "Item" + index,
            Token = 0, Attributes = TypeAttributes.Public, IsValueType = false, IsEnum = false }, []);
        var types = new[] { Type(1), Type(2) };
        var pointer = new Variable(Storage.Gpr(0), 3);
        var created = new Variable(Storage.Gpr(0), 4);
        MachineFunction Sample(bool conditional = false, bool handler = false, bool preceding = false, bool unrelated = false)
        {
            var first = new Block(0x1010) { Statements = [new Define(0x1010, pointer with { Version = 1 }, new Symbol(SymbolKind.Class, types[0])), new Jump(0x1014, 0x1030)] };
            var second = new Block(0x1020) { Statements = [new Define(0x1020, pointer with { Version = 2 }, new Symbol(SymbolKind.Class, types[1])), new Jump(0x1024, 0x1030)] };
            var allocation = new Call(0x1034, CallKind.Direct, Expr.C(0x2000, 64)) { Op = new(OpKind.NewObject, null),
                Arguments = [new Use(pointer, 64)], Sources = [Storage.Gpr(0)], Defines = [created], Results = [Storage.Gpr(0)] };
            var ctor = new Call(0x1038, CallKind.Direct, Expr.C(0x3000, 64)) { Sources = [Storage.Gpr(0), Storage.Gpr(1)],
                Arguments = [new Use(unrelated ? pointer : created, 64), Expr.C(0, 64)] };
            var merge = new Block(0x1030) { Statements = [new Phi(0x1030, pointer, [pointer with { Version = 1 }, pointer with { Version = 2 }]),
                allocation, ctor, new Return(0x103c) { Value = new Use(created, 64) }] };
            var entry = new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), first.Start, second.Start)] };
            var exit = new Block(0x1040) { Statements = [new Return(0x1040)] };
            MachineFunction.AddEdge(entry, first);
            MachineFunction.AddEdge(entry, second);
            MachineFunction.AddEdge(first, merge);
            MachineFunction.AddEdge(second, merge);
            if (conditional)
            {
                first.Statements[^1] = new Branch(0x1014, Expr.C(1, 1), merge.Start, exit.Start);
                MachineFunction.AddEdge(first, exit);
            }
            if (handler) first.Handler = exit;
            if (preceding) merge.Statements.Insert(1, new Store(0x1032, Expr.C(0, 64), Expr.C(1, 64)));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1044, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, first, second, merge, exit] };
            function.Renumber();
            return function;
        }
        var a = new Assertions();
        var next = -1;
        bool Run(MachineFunction function, bool known = true) => ClassPhiAllocations.Run(function, address => known && address == 0x3000, () => new(Storage.Temp(next--), 1));
        var valid = Sample();
        a.True(Run(valid), "类型选择改为对象选择");
        a.True(valid.Blocks.Single(b => b.Start == 0x1010).Statements is [Define, Call { Op.Operand: DefinitionRef type, Defines: [var value] },
            Call { Arguments: [Use receiver, Const] }, Jump] && type == types[0] && receiver.Variable == value, "分支保持分配和构造顺序及接收者");
        a.True(valid.Blocks.Single(b => b.Start == 0x1030).Statements is [Phi, Phi { Target: var result }, Return] && result == created, "合流结果保留原变量");
        a.True(!Run(Sample(conditional: true)), "有额外出口时不提前分配");
        a.True(!Run(Sample(handler: true)), "不跨异常区域");
        a.True(!Run(Sample(preceding: true)), "不跨可观察操作");
        a.True(!Run(Sample(unrelated: true)) && !Run(Sample(), known: false), "必须紧邻已知的构造调用且接收者相同");
        return a.Finish("class-phi-allocations");
    }
}
