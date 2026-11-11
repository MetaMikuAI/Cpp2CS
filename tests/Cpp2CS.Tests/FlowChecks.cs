using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
namespace Cpp2CS.Tests;
internal static class FlowChecks
{
    public const string Command = "flow";
    public static int Run()
    {
        var a = new Assertions(); var q = new FlowQueries(); var t = new TermTable();
        var x = new BlockIdentity(); var y = new BlockIdentity(); var z = new BlockIdentity(); var end = new BlockIdentity();
        QueryContext Context(params Block[] blocks)
        {
            var builder = new FunctionBuilder(t, x, 64, new(t.Atom(new RootAtom(AddressRoot.Frame), 64)));
            builder.Blocks.AddRange(blocks); return new(builder.Freeze());
        }
        var line = Context(new(x, [], [], new Jump(y)), new(y, [], [], new Return([])));
        a.True(line.Get(q.Dominates, new(x, y)).Value && line.Get(q.PostDominates, new(y, x)).Value, "直线支配与后支配");
        var diamond = Context(new(x, [], [], new Branch(t.Constant(1, 1), y, z)), new(y, [], [], new Jump(end)), new(z, [], [], new Jump(end)), new(end, [], [], new Return([])));
        a.True(diamond.Get(q.Dominates, new(x, end)).Value && !diamond.Get(q.Dominates, new(y, end)).Value && diamond.Get(q.PostDominates, new(end, x)).Value, "菱形保留两条路径");
        var loop = Context(new(x, [], [], new Jump(y)), new(y, [], [], new Branch(t.Constant(1, 1), y, end)), new(end, [], [], new Return([])));
        a.True(loop.Get(q.Dominates, new(y, end)).Value && loop.Get(q.PostDominates, new(end, y)).Value, "循环的终结路径经过出口");
        var exits = Context(new(x, [], [], new Branch(t.Constant(1, 1), y, z)), new(y, [], [], new Return([])), new(z, [], [], new Return([])));
        a.True(!exits.Get(q.PostDominates, new(y, x)).Value, "多出口没有单个必经出口");
        var call = new Call(new(), new ImageFunction(1), [], [], Unwind: z);
        var exception = Context(new(x, [], [call, new MemoryWrite(new(), t.Constant(0,64), 8, t.Constant(1,8))], new Jump(y)), new(y, [], [], new Return([])), new(z, [], [], new Return([])));
        a.True(exception.Get(q.PointDominates, new(new(x,0), new(x,1))).Value && !exception.Get(q.PointDominates, new(new(x,1), new(x,1))).Value && !exception.Get(q.PostDominates, new(y,x)).Value, "调用正常返回次序与异常出口");
        return a.Finish("控制流查询");
    }
}
