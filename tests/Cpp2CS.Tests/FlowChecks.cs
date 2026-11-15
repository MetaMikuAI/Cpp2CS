using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
namespace Cpp2CS.Tests;
internal static class FlowChecks
{
    public const string Command = "flow";
    private sealed class Exits(params FlowEdge[] exits) : Query<FlowEdge, bool>
    {
        public override Outcome<bool> Compute(QueryContext context, FlowEdge key) => Outcome<bool>.Success(exits.Contains(key));
    }
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
        a.True(exception.Get(q.Graph, 0).Value.Reachable.Contains(z)
            && exception.Get(q.Dominates, new(x,z)).Value
            && exception.Get(q.PointDominates, new(new(x,0),new(z,0))).Value
            && !exception.Get(q.PointDominates, new(new(x,1),new(z,0))).Value,
            "展开边参与可达与支配，调用后程序点不支配处理入口");
        var normal = new FlowQueries(includeUnwind: false);
        a.True(!exception.Get(normal.Graph, 0).Value.Reachable.Contains(z)
            && exception.Get(normal.PostDominates, new(y,x)).Value, "正常控制流视图单独计算可达与支配");
        var escaping = Context(new(x,[],[call with { Unwind = null }],new Jump(y)),new(y,[],[],new Return([])));
        a.True(escaping.Get(normal.PostDominates,new(y,x)).Value && !escaping.Get(q.PostDominates,new(y,x)).Value,
            "正常控制流视图不把调用的异常离开计作正常出口");
        var sharedCold = new BlockIdentity(); var outside = new BlockIdentity();
        var firstRead = new MemoryRead(new(), t.Constant(16, 64), 32, t.Constant(0, 32));
        var regionContext = Context(new(x, [], [firstRead], new Branch(t.Constant(1, 1), y, sharedCold)),
            new(y, [], [], new Branch(t.Constant(1, 1), z, end)), new(z, [], [], new Jump(end)),
            new(outside, [], [], new Jump(sharedCold)), new(sharedCold, [], [], new Unreachable()), new(end, [], [], new Return([])));
        var excluded = new Exits(new FlowEdge(x, sharedCold));
        a.True(!regionContext.Get(new SnapshotRegionQuery(normal), new(x, end)).IsSuccess,
            "没有出口凭据时共享冷块不属于单续点区域");
        var proved = regionContext.Get(new SnapshotRegionQuery(normal, excluded), new(x, end));
        a.True(proved.IsSuccess && proved.Value.Order.ToHashSet().SetEquals([y, z]), "已认定的失败出口不纳入区域，不要求冷块独占");
        var regionPaths = regionContext.Get(new SnapshotPathsQuery(normal, excluded), new(new(x, 0), end));
        a.True(regionPaths.IsSuccess && regionPaths.Value.Length == 2 && regionPaths.Value.All(p => p.Points.SequenceEqual([new Point(x, 0)])),
            "路径展开保留入口程序点和两条正常路径");
        a.True(!regionContext.Get(new SnapshotPathsQuery(normal, excluded, pathBudget: 1), new(new(x, 0), end)).IsSuccess,
            "路径数超过预算时报洞");
        a.True(!loop.Get(new SnapshotRegionQuery(normal), new(x, end)).IsSuccess, "无环区域拒绝循环");
        var secondEntry = Context(new(x, [], [], new Branch(t.Constant(1, 1), y, z)), new(y, [], [], new Jump(end)),
            new(z, [], [], new Jump(end)), new(outside, [], [], new Jump(y)), new(end, [], [], new Return([])));
        a.True(!secondEntry.Get(new SnapshotRegionQuery(normal, new Exits()), new(x, end)).IsSuccess, "带失败出口的区域仍拒绝第二入口");
        return a.Finish("控制流查询");
    }
}
