using Cpp2CS.Ir;
using Cpp2CS.Model;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class AsyncBranchCopyCheck
{
    [Command("async-branch-copies", "异步续接路径的局部赋值与并行复制", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions(); var integer = new PrimitiveRef("I4");
        LocalValue Local(int index) => new(new(Storage.Temp(index), 1), integer, 32);
        var x = Local(1); var y = Local(2); var z = Local(3);
        var blocks = new Dictionary<ulong, List<ManagedStatement>>();
        ManagedJump Jump(ulong target, params ManagedCopy[] copies) => new(0, new(target, copies));
        bool Pure(ManagedValue value) => value is LocalValue or ConstantValue;
        bool Same(ManagedEdge left, ManagedEdge right) => AsyncBranchCopies.Equivalent(left, right, blocks, Pure);
        blocks[1] = [new ManagedAssignment(1, x, y), Jump(3)];
        blocks[2] = [Jump(3, new ManagedCopy(x, y))];
        a.True(Same(new(1, []), new(2, [])), "局部复制与相同 phi 复制等价");
        blocks[1] = [new ManagedAssignment(1, x, z), new ManagedAssignment(2, x, y), Jump(3)];
        a.True(Same(new(1, []), new(2, [])), "中间纯赋值被覆盖后比较最终值");
        blocks[1] = [new ManagedAssignment(1, x, z), Jump(3)];
        a.True(!Same(new(1, []), new(2, [])), "不同最终值保留分支");
        a.True(!Same(new(3, [new(x, y), new(y, x)]), new(3, [new(x, y), new(y, y)])), "并行交换不能按逐条赋值解释");
        a.True(Same(new(3, [new(x, y), new(y, x)]), new(3, [new(y, x), new(x, y)])), "并行复制顺序不影响结果");
        blocks[1] = [new ManagedCall(1, new(null!, null, [], false), null, false), Jump(3)];
        a.True(!Same(new(1, []), new(3, [])), "不跨越调用或潜在异常");
        blocks[1] = [Jump(1)];
        a.True(!Same(new(1, []), new(3, [])), "纯跳转环不能当作到达续接点");
        blocks[1] = [new ManagedAssignment(1, x, new IndirectValue(new AddressValue(y), integer)), Jump(3)];
        a.True(!Same(new(1, []), new(3, [])), "可能抛出的间接读取不参与路径消除");
        return a.Finish("async-branch-copies");
    }
}
