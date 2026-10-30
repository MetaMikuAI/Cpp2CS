using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class NullPathCheck
{
    [Command("null-path", "判空路径上的 SSA 引用恢复", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var value = new Use(new Variable(Storage.Gpr(0), 1), 64);
        foreach (var condition in new[] { Cond.Eq, Cond.Ne })
        {
            var entry = new Block(0) { Statements = [new Branch(4, new Compare(condition, value, new Const(0, 64)),
                condition == Cond.Eq ? 16UL : 32UL, condition == Cond.Eq ? 32UL : 16UL)] };
            var zero = new Block(16) { Statements = [new Return(20) { Value = value }] };
            var other = new Block(32) { Statements = [new Return(36) { Value = value }] };
            MachineFunction.AddEdge(entry, condition == Cond.Eq ? zero : other);
            MachineFunction.AddEdge(entry, condition == Cond.Eq ? other : zero);
            var function = new MachineFunction { Entry = 0, Range = null!, Blocks = [entry, zero, other] };
            function.Renumber();
            var facts = new NullPathFacts(function);
            a.True(facts.IsNull(value, 20), $"{condition} 零分支");
            a.True(!facts.IsNull(value, 36), $"{condition} 非零分支不变");
            a.True(!facts.IsNull(value with { Variable = value.Variable with { Version = 2 } }, 20), $"{condition} 新 SSA 值不继承旧事实");
            MachineFunction.AddEdge(other, zero);
            function.Renumber();
            a.True(!new NullPathFacts(function).IsNull(value, 20), $"{condition} 合流不能使用单边事实");
            MachineFunction.RemoveEdge(other, zero);
            entry.Statements = [new Branch(4, new Compare(condition, value with { Width = 32 }, new Const(0, 32)),
                condition == Cond.Eq ? 16UL : 32UL, condition == Cond.Eq ? 32UL : 16UL)];
            a.True(!new NullPathFacts(function).IsNull(value, 20), $"{condition} 低 32 位为零不代表引用为空");
        }
        return a.Finish("null-path");
    }
}
