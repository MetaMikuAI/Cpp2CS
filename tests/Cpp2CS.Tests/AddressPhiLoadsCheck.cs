using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
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
        var indexed = Sample();
        indexed.Blocks.Single(b => b.Start == 0x1010).Statements[0] = new Define(0x1010, pointer with { Version = 1 },
            new Binary(BinOp.Add, Expr.C(0x3000, 64), Expr.C(0x80, 64), 64));
        indexed.Blocks.Single(b => b.Start == 0x1020).Statements[0] = new Define(0x1020, pointer with { Version = 2 }, Expr.C(0x4000, 64));
        var join = indexed.Blocks.Single(b => b.Start == 0x1030);
        var index = new Variable(Storage.Gpr(9), 3);
        var leftIndex = index with { Version = 1 };
        var rightIndex = index with { Version = 2 };
        join.Statements.Insert(1, new Phi(join.Start, index, [leftIndex, rightIndex]));
        var address = new Binary(BinOp.Add, new Use(pointer, 64), new Binary(BinOp.Shl, new Use(index, 64), Expr.C(2, 64), 64), 64);
        join.Statements[2] = new Define(join.Start, result, new Cpp2CS.Ir.Convert(ConvKind.ZeroExtend, new Load(address, 32), 128));
        a.True(Run(indexed), "基址和索引分别合流的向量寄存器读取可以分配到前驱");
        a.True(indexed.Blocks.Single(b => b.Start == 0x1010).Statements.OfType<Define>().Any(d => d.Value is Cpp2CS.Ir.Convert { Width: 128, Operand: Load { Width: 32, Address: Binary { Right: Const { Value: 0x3080 } } at } }
            && ExprMap.Walk(at).OfType<Use>().Any(u => u.Variable == leftIndex)
            && !ExprMap.Walk(at).OfType<Use>().Any(u => u.Variable == rightIndex)), "左侧表地址配左侧索引，并保留加载位宽和扩展");
        a.True(indexed.Blocks.Single(b => b.Start == 0x1020).Statements.OfType<Define>().Any(d => d.Value is Cpp2CS.Ir.Convert { Operand: Load { Address: Binary { Right: Const { Value: 0x4000 } } at } }
            && ExprMap.Walk(at).OfType<Use>().Any(u => u.Variable == rightIndex)
            && !ExprMap.Walk(at).OfType<Use>().Any(u => u.Variable == leftIndex)), "右侧索引不与左侧来源交叉");
        var nestedRead = Sample();
        var nestedJoin = nestedRead.Blocks.Single(b => b.Start == 0x1030);
        nestedJoin.Statements[1] = new Define(nestedJoin.Start, result, new Load(new Binary(BinOp.Add,
            new Use(pointer, 64), new Load(new Use(new(Storage.Gpr(7), 0), 64), 64), 64), 64));
        a.True(!Run(nestedRead), "地址含额外内存读取时不改变求值位置");
        var fieldRead = Sample();
        var fieldJoin = fieldRead.Blocks.Single(b => b.Start == 0x1030);
        fieldJoin.Statements[1] = new Define(fieldJoin.Start, result,
            new Load(new Binary(BinOp.Add, new Use(pointer, 64), Expr.C(16, 64), 64), 64));
        a.True(!Run(fieldRead), "普通字段读取不套用常量表扩展，保留访问器认回形态");
        MachineFunction Guarded(bool otherEntry = false, bool interveningCall = false)
        {
            var function = Sample();
            var merge = function.Blocks.Single(b => b.Start == 0x1030);
            var source = merge.Statements.OfType<Define>().Single();
            var length = new Variable(Storage.Gpr(11), 1);
            var destination = new Use(new(Storage.Gpr(12), 0), 64);
            var check = new Block(0x1050) { Statements = [
                new Define(0x1050, length, new Load(new Binary(BinOp.Add, destination, Expr.C(RuntimeLayout.ArrayMaxLength, 64), 64), 32)),
                new Call(0x1054, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.BoundsCheck, null), Arguments = [Expr.C(0, 32), new Use(length, 32)] },
                new Jump(0x1058, 0x1060)] };
            var read = new Block(0x1060) { Statements = [source, new Return(0x1064) { Value = new Use(result, 64) }] };
            merge.Statements.RemoveAll(s => s is not Phi);
            merge.Statements.Add(new Call(0x1030, CallKind.Direct, Expr.C(0, 64)) { Op = new(OpKind.NullCheck, null), Arguments = [destination] });
            merge.Statements.Add(new Jump(0x1034, check.Start));
            MachineFunction.AddEdge(merge, check);
            MachineFunction.AddEdge(check, read);
            if (otherEntry) MachineFunction.AddEdge(function.EntryBlock, read);
            if (interveningCall) check.Statements.Insert(1, new Call(0x1052, CallKind.Direct, Expr.C(0x2000, 64)));
            function.Blocks.AddRange([check, read]);
            function.Renumber();
            return function;
        }
        var guarded = Guarded();
        a.True(Run(guarded), "检查链与地址合流读取沿原入边一起分配");
        a.True(guarded.Blocks.Single(b => b.Start == 0x1010).Statements is [Define, Call { Op.Kind: OpKind.NullCheck },
            Define { Value: Load }, Call { Op.Kind: OpKind.BoundsCheck }, Define { Value: Load }, Jump], "保留判空、读取长度、边界检查和读取值的原始顺序");
        a.True(!Run(Guarded(otherEntry: true)), "读取块有其他入口时不移动检查链");
        a.True(!Run(Guarded(interveningCall: true)), "检查链中的普通调用阻止分配");
        return a.Finish("address-phi-loads");
    }
}
