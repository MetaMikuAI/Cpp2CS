using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class AsyncConstantBranchCheck
{
    [Command("async-constant-branches", "异步路由标志的有限取值与条件边", Gate = Gate.Unit)]
    public static int Run()
    {
        var integer = new PrimitiveRef("I4"); var boolean = new PrimitiveRef("Boolean");
        var local = new LocalValue(new(Storage.Temp(1), 1), integer, 32);
        ConstantValue Number(ulong value) => new(value, integer, 32);
        ManagedValue Equal(ulong value) => new ComparisonValue(Cond.Eq, local, Number(value), boolean);
        ulong? Eval(ManagedValue value, Dictionary<Variable, ulong> known) => value switch
        {
            ConstantValue c => c.Bits,
            LocalValue l => known.TryGetValue(l.Variable, out var x) ? x : null,
            ComparisonValue c when Eval(c.Left, known) is { } left && Eval(c.Right, known) is { } right => left == right ? 1UL : 0UL,
            _ => null,
        };
        Dictionary<ulong, List<ManagedStatement>> Blocks(bool missing = false) => new()
        {
            [0] = [new ManagedBranch(0, new ArgumentValue(0, boolean, 32), new(1, []), new(2, []))],
            [1] = [new ManagedAssignment(1, local, Number(7)), new ManagedJump(1, new(3, []))],
            [2] = missing ? [new ManagedJump(2, new(3, []))] : [new ManagedAssignment(2, local, Number(9)), new ManagedJump(2, new(3, []))],
            [3] = [new ManagedBranch(3, Equal(7), new(4, []), new(5, []))],
            [4] = [new ManagedReturn(4, Number(1))],
            [5] = [new ManagedBranch(5, Equal(9), new(4, []), new(6, []))],
            [6] = [new ManagedReturn(6, null)],
        };
        var a = new Assertions();
        var body = Blocks();
        AsyncConstantBranches.Run(body, 0, [], Eval);
        a.True(body[3][0] is ManagedBranch, "多个合法值仍保留必要分支");
        a.True(body[5][0] is ManagedJump { Edge.Target: 4 }, "排除第一个值后，第二次比较必然成功");
        var missing = Blocks(true);
        AsyncConstantBranches.Run(missing, 0, [], Eval);
        a.True(missing[5][0] is ManagedBranch, "一条路径没有常量赋值时不能折叠");
        var overwritten = Blocks();
        overwritten[3].Insert(0, new ManagedAssignment(3, local, new ArgumentValue(1, integer, 32)));
        AsyncConstantBranches.Run(overwritten, 0, [], Eval);
        a.True(overwritten[5][0] is ManagedBranch, "未知值覆盖常量集合");
        var caught = Blocks();
        AsyncConstantBranches.Run(caught, 0, [new([1], 5, [5], null, ManagedRegionKind.Catch)], Eval);
        a.True(caught[5][0] is ManagedBranch, "异常边不借用抛出之后的正常路径常量");
        var other = new LocalValue(new(Storage.Temp(2), 1), integer, 32);
        var parallel = new Dictionary<ulong, List<ManagedStatement>>
        {
            [0] = [new ManagedAssignment(0, local, Number(7)), new ManagedAssignment(0, other, Number(9)),
                new ManagedJump(0, new(1, [new(local, other), new(other, local)]))],
            [1] = [new ManagedBranch(1, Equal(9), new(2, []), new(3, []))],
            [2] = [new ManagedBranch(2, new ComparisonValue(Cond.Eq, other, Number(7), boolean), new(3, []), new(4, []))],
            [3] = [new ManagedReturn(3, Number(1))], [4] = [new ManagedReturn(4, Number(0))],
        };
        AsyncConstantBranches.Run(parallel, 0, [], Eval);
        a.True(parallel[1][0] is ManagedJump { Edge.Target: 2 } && parallel[2][0] is ManagedJump { Edge.Target: 3 }, "边上的交换按并行复制求值");
        return a.Finish("async-constant-branches");
    }
}
