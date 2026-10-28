using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class AddressPhiLoadsCheck
{
    [Command("address-phi-loads", "地址合流读取的顺序与异常边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var pointer = new Variable(Storage.Gpr(8), 3);
        var result = new Variable(Storage.Gpr(0), 1);
        MachineFunction Sample(bool conditional = false, bool handler = false, bool precedingRead = false, bool otherPhi = false)
        {
            var first = new Block(0x1010) { Statements = [new Define(0x1010, pointer with { Version = 1 },
                new Binary(BinOp.Add, new Use(new(Storage.Gpr(1), 0), 64), Expr.C(32, 64), 64))] };
            var second = new Block(0x1020) { Statements = [new Define(0x1020, pointer with { Version = 2 }, new Use(new(Storage.Gpr(2), 0), 64))] };
            var merge = new Block(0x1030) { Statements = [new Phi(0x1030, pointer, [pointer with { Version = 1 }, pointer with { Version = 2 }]),
                new Define(0x1030, result, new Load(new Use(pointer, 64), 64)), new Return(0x1034) { Value = new Use(result, 64) }] };
            var entry = new Block(0x1000) { Statements = [new Branch(0x1000, Expr.C(1, 1), first.Start, second.Start)] };
            var exit = new Block(0x1040) { Statements = [new Return(0x1040)] };
            first.Statements.Add(conditional ? new Branch(0x1014, Expr.C(1, 1), merge.Start, exit.Start) : new Jump(0x1014, merge.Start));
            second.Statements.Add(new Jump(0x1024, merge.Start));
            MachineFunction.AddEdge(entry, first);
            MachineFunction.AddEdge(entry, second);
            MachineFunction.AddEdge(first, merge);
            MachineFunction.AddEdge(second, merge);
            if (conditional) MachineFunction.AddEdge(first, exit);
            if (handler) first.Handler = exit;
            if (precedingRead) merge.Statements.Insert(1, new Define(0x102c, new(Storage.Gpr(3), 1), new Load(Expr.C(0, 64), 64)));
            if (otherPhi)
            {
                var alias = new Variable(Storage.Gpr(4), 1);
                merge.Statements.Insert(0, new Phi(0x1030, alias, [new(Storage.Gpr(5), 0), new(Storage.Gpr(6), 0)]));
                first.Statements[0] = new Define(0x1010, pointer with { Version = 1 }, new Use(alias, 64));
            }
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1044, CodeRegion.Managed, BoundaryEvidence.EhFrame),
                Blocks = [entry, first, second, merge, exit] };
            function.Renumber();
            return function;
        }
        var a = new Assertions();
        var next = -1;
        bool Run(MachineFunction function) => AddressPhiLoads.Run(function, () => new(Storage.Temp(next--), 1));
        var valid = Sample();
        a.True(Run(valid), "首个读取从地址合流改为值合流");
        a.True(valid.Blocks.Single(b => b.Start == 0x1010).Statements is [Define, Define { Value: Load { Address: Binary } }, Jump], "保留数组地址计算，读取位于跳转前");
        a.True(valid.Blocks.Single(b => b.Start == 0x1030).Statements is [Phi, Phi { Target: var target }, Return] && target == result, "结果保留原变量与前驱顺序");
        a.True(!Run(Sample(conditional: true)), "前驱另有出口时不提前读取");
        a.True(!Run(Sample(handler: true)), "不跨越异常区域");
        a.True(!Run(Sample(precedingRead: true)), "不跨越更早的内存读取");
        a.True(!Run(Sample(otherPhi: true)), "不把合流处才定义的值提前到前驱");
        var selected = Sample();
        var parent = selected.Blocks.Single(b => b.Start == 0x1010);
        var original = (Define)parent.Statements[0];
        var choice = new Select(new Compare(Cond.Eq, new Use(new(Storage.Gpr(7), 0), 32), Expr.C(0, 32)), Expr.C(0x3000, 64), Expr.C(0x4000, 64), 64);
        parent.Statements[0] = original with { Value = choice };
        a.True(Run(selected), "只读表生成的纯地址选择允许继续分配外层读取");
        a.True(parent.Statements.OfType<Define>().Any(d => d.Value is Load { Address: Select }), "选择在原必经前驱中求值，不提前到分支之外");
        var repeated = Sample();
        repeated.Blocks.Single(b => b.Start == 0x1010).Statements[0] = original with
            { Value = choice with { Condition = new Load(Expr.C(0x2000, 64), 1) } };
        a.True(Run(repeated) && repeated.Blocks.Single(b => b.Start == 0x1010).Statements.OfType<Define>()
            .Any(d => d.Value is Load { Address: Use use } && use.Variable == original.Target), "条件含内存读取时保留原指针快照，不复制选择表达式");
        return a.Finish("address-phi-loads");
    }
}
