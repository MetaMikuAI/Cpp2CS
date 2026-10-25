using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class StateDispatchCheck
{
    [Command("state-dispatch", "状态分派的分支合并、常量和调用身份边界", Gate = Gate.Unit)]
    public static int Run()
    {
        Expr self = new Use(new(Storage.Gpr(0), 0), 64);
        StateDispatch Read(bool merged, uint state = 1, ulong target = 0x8000)
        {
            Expr receiver = merged ? new Load(new Load(self, 64), 64) : self;
            var field = new Load(new Binary(BinOp.Add, receiver, Expr.C(16, 64), 64), 32);
            Expr first = new Compare(Cond.Eq, field, Expr.C(state, 32));
            Expr second = new Compare(Cond.Eq, new Binary(BinOp.Add, field, Expr.C(3, 32), 32), Expr.C(0, 32));
            var blocks = new List<Block>
            {
                new(0x1000) { Statements = [new Branch(0x1000, merged ? new Logical(false, first, second) : first, 0x1020, merged ? 0x1030UL : 0x1010UL)] },
                new(0x1020) { Statements = [new Call(0x1020, CallKind.Tail, Expr.C(target, 64)) { Arguments = [receiver], Sources = [Storage.Gpr(0)] }] },
                new(0x1030) { Statements = [new Return(0x1030)] }
            };
            if (!merged) blocks.Add(new(0x1010) { Statements = [new Branch(0x1010, second, 0x1020, 0x1030)] });
            var function = new MachineFunction { Entry = 0x1000, Range = new(0x1000, 0x1040, CodeRegion.Managed, default), Blocks = blocks };
            return StateDispatch.Read(function, c => c)!;
        }
        var a = new Assertions();
        var original = Read(false);
        a.True(original.Same(Read(true)), "两条分支与合并条件具有相同状态分区");
        a.True(!original.Same(Read(true, 2)), "状态值改变不能视为同一清理");
        a.True(!original.Same(Read(true, target: 0x9000)), "清理调用目标改变不能匹配");
        a.Equal(0, original.Otherwise.Length, "其他状态不调用清理");
        return a.Finish("state-dispatch");
    }
}
