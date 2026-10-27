using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Idioms;
using Cpp2CS.Ir;

namespace Cpp2CS.Tests;

internal static class SelectedAddressLoadsCheck
{
    [Command("selected-address-loads", "常量地址选择的读取值及求值边界", Gate = Gate.Unit)]
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
        a.True(!SelectedAddressLoads.Run(Sample(32, choice with { True = new Use(result, 64) })), "非固定偏移不展开");
        a.True(!SelectedAddressLoads.Run(Sample(32, loadBase: true)), "不重复读取地址基址");
        a.True(!SelectedAddressLoads.Run(Sample(32, store: true)), "不把写入目标改成值选择");
        return a.Finish("selected-address-loads");
    }
}
