using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class SelectedAddressLoadsCheck
{
    [Command("selected-address-loads", "条件地址读取的位宽、单臂求值和副作用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var offset = new Variable(Storage.Gpr(8), 1);
        var result = new Variable(Storage.Gpr(0), 1);
        var choice = new Select(new Compare(Cond.Eq, new Read(Storage.Gpr(1), 32), Expr.C(0, 32)), Expr.C(16, 64), Expr.C(24, 64), 64);
        MachineFunction Sample(int width, Expr? selected = null, bool loadBase = false, bool store = false)
        {
            var address = new Binary(BinOp.Add, loadBase ? new Load(Expr.C(0x1000, 64), 64) : Expr.C(0x1000, 64), new Use(offset, 64), 64);
            return new() { Entry = 0, Range = new(0, 12, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [new(0)
                { Statements = [new Define(0, offset, selected ?? choice), store ? new Store(4, address, Expr.C(3, width)) : new Define(4, result, new Load(address, width)), new Return(8)] }] };
        }
        var a = new Assertions();
        foreach (var width in new[] { 8, 32, 64 })
        {
            var sample = Sample(width);
            a.True(SelectedAddressLoads.Run(sample), "常量地址选择转换为值选择");
            var expression = ((Define)sample.Blocks[0].Statements[1]).Value;
            foreach (var flag in new uint[] { 0, 1 })
            {
                var evaluator = new Evaluator();
                evaluator.Registers[Storage.Gpr(1)] = flag;
                var expected = evaluator.Eval(new Load(Expr.C(flag == 0 ? 0x1010u : 0x1018u, 64), width));
                a.Equal(expected, evaluator.Eval(expression), "只读取所选地址，保留读取位宽");
                a.True(evaluator.Failure is null, "结果可求值");
            }
        }
        a.True(!SelectedAddressLoads.Run(Sample(32, choice with { Condition = new Load(Expr.C(0x2000, 64), 8) })), "不重读条件中的内存");
        a.True(!SelectedAddressLoads.Run(Sample(32, choice with { True = new Load(Expr.C(0x2000, 64), 64) })), "不重读地址分支中的内存");
        a.True(!SelectedAddressLoads.Run(Sample(32, choice with { False = new Unknown("address", 64) })), "不消除未知地址求值");
        a.True(!SelectedAddressLoads.Run(Sample(32, loadBase: true)), "不重复读取地址基址");
        a.True(!SelectedAddressLoads.Run(Sample(32, store: true)), "不把写入目标改成值选择");
        foreach (var width in new[] { 8, 32, 64 })
        {
            var sample = Sample(width, choice with { True = new Binary(BinOp.Add, new Read(Storage.Gpr(2), 64), Expr.C(16, 64), 64) });
            a.True(SelectedAddressLoads.Run(sample), "不同存储根的地址可以选择");
            var expression = ((Define)sample.Blocks[0].Statements[1]).Value;
            foreach (var flag in new uint[] { 0, 1 })
            {
                var evaluator = new Evaluator();
                evaluator.Registers[Storage.Gpr(1)] = flag;
                evaluator.Registers[Storage.Gpr(2)] = 0x500;
                var expected = evaluator.Eval(new Load(Expr.C(flag == 0 ? 0x1510u : 0x1018u, 64), width));
                a.Equal(expected, evaluator.Eval(expression), "地址分支保留各自的基址与偏移");
                a.True(evaluator.Failure is null, "动态地址选择可求值");
            }
        }
        var condition = new Compare(Cond.Eq, new Use(new(Storage.Gpr(1), 1), 32), Expr.C(0, 32));
        foreach (var taken in new[] { false, true })
        {
            var sample = Sample(64, choice with { Condition = condition });
            var entry = sample.Blocks[0];
            var read = entry.Statements[1];
            var path = new Block(12) { Statements = [new Jump(12, 24)] };
            var other = new Block(20) { Statements = [new Return(20)] };
            var load = new Block(24) { Statements = [read, new Return(28)] };
            entry.Statements = [entry.Statements[0], new Branch(8, condition, taken ? 12UL : 20UL, taken ? 20UL : 12UL)];
            sample.Blocks.AddRange([path, other, load]);
            MachineFunction.AddEdge(entry, taken ? path : other);
            MachineFunction.AddEdge(entry, taken ? other : path);
            MachineFunction.AddEdge(path, load);
            a.True(SelectedAddressLoads.Run(sample), "分支后的条件地址被归约");
            a.Equal<Expr>(new Load(Expr.C(taken ? 0x1010UL : 0x1018UL, 64), 64), ((Define)load.Statements[0]).Value,
                "唯一前驱路径确认所选地址，另一臂不再参与类型恢复");
            load.Statements[0] = ((Define)read) with { Value = new Select(condition,
                new Load(Expr.C(0x1010, 64), 64), new Load(Expr.C(0x1018, 64), 64), 64) };
            a.True(SelectedAddressLoads.Run(sample), "已分配到两臂的条件加载仍使用路径事实");
            a.Equal<Expr>(new Load(Expr.C(taken ? 0x1010UL : 0x1018UL, 64), 64), ((Define)load.Statements[0]).Value,
                "先前归约产生的选择保留实际执行的加载");
            var invocation = new Call(26, CallKind.Direct, Expr.C(0x2000, 64)) { Arguments = [new Use(offset, 64)] };
            load.Statements.Insert(1, invocation);
            SelectedAddressLoads.Run(sample);
            a.Equal<Expr>(Expr.C(taken ? 16UL : 24UL, 64), ((Call)load.Statements[1]).Arguments[0], "调用使用路径上确定的同一引用，避免类指针与接收者身份分裂");
            load.Statements.RemoveAt(1);
            load.Statements[0] = read;
            other.Statements = [new Jump(20, 24)];
            MachineFunction.AddEdge(other, load);
            SelectedAddressLoads.Run(sample);
            a.True(((Define)load.Statements[0]).Value is Select, "合流后的读取不继承单边条件");
            MachineFunction.RemoveEdgeAt(other, 0);
            load.Statements[0] = read;
            entry.Statements[1] = new Branch(8, condition with { Left = new Use(new(Storage.Gpr(1), 2), 32) }, taken ? 12UL : 20UL, taken ? 20UL : 12UL);
            SelectedAddressLoads.Run(sample);
            a.True(((Define)load.Statements[0]).Value is Select, "相同寄存器的不同 SSA 版本不能共享条件");
        }
        return a.Finish("selected-address-loads");
    }
}
