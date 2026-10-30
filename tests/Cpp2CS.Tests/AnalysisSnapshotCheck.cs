using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Tests;

internal static class AnalysisSnapshotCheck
{
    [Command("analysis-snapshot", "IR 改写使定义缓存失效，原快照的语句序列保持稳定", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var variable = new Variable(Storage.Gpr(0), 1);
        var block = new Block(0x100) { Statements = [new Define(0x100, variable, Expr.C(1, 64))] };
        var store = new MethodAnalyses();
        a.True(store.Refresh([block], new Dictionary<Variable, Phi>()), "首次创建");
        var snapshot = store.Snapshot!;
        var original = store.Get(Definitions.Analysis);
        a.True(ReferenceEquals(original, store.Get(Definitions.Analysis)), "同版本复用");
        block.Statements[0] = new Define(0x100, variable, Expr.C(2, 64));
        a.True(store.Refresh([block], new Dictionary<Variable, Phi>()), "改写后失效");
        a.Equal(2, store.Version, "版本推进");
        a.True(original.Values[variable] is Const { Value: 1 } && store.Get(Definitions.Analysis).Values[variable] is Const { Value: 2 }, "新旧索引分离");
        a.True(snapshot.View.Statements.Single() is Define { Value: Const { Value: 1 } }, "原快照保留来源");
        a.True(!store.Refresh([block], new Dictionary<Variable, Phi>()), "未变更不失效");
        block.IsLandingPad = true;
        a.True(store.Refresh([block], new Dictionary<Variable, Phi>()), "异常入口变化失效");
        var sources = new[] { variable };
        block.Statements.Add(new Phi(0x104, new Variable(Storage.Gpr(1), 1), sources));
        store.Refresh([block], new Dictionary<Variable, Phi>());
        sources[0] = new Variable(Storage.Gpr(0), 2);
        var rejected = false;
        try { store.Refresh([block], new Dictionary<Variable, Phi>()); }
        catch (InvalidOperationException) { rejected = true; }
        a.True(rejected, "禁止原地修改已发布节点的数组");
        return a.Finish("analysis-snapshot");
    }
}
