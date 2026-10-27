using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

/// <summary>用合成 CFG 固定直线链、异常去向和可观察顺序的边界，不依赖某个被恢复方法。</summary>
internal static class PairingCheck
{
    [Command("pairing", "T2 跨块配对的控制流、异常与时序边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var created = new Variable(Storage.Gpr(0), 1);
        var allocation = new Call(4, CallKind.Direct, Expr.C(100, 64));
        var constructor = new Call(20, CallKind.Direct, Expr.C(200, 64));
        var first = new Block(0) { Statements = [allocation] };
        var last = new Block(16) { Statements = [constructor, new Return(24)] };
        MachineFunction.AddEdge(first, last);
        bool Reaches() => AllocationPairing.Following(first, 0).Any(p => ReferenceEquals(p.Statement, constructor));
        a.True(Reaches(), "调用切块后的唯一正常后继可达");
        var pad = new Block(80) { IsLandingPad = true };
        first.Handler = pad; first.Successors.Add(pad); pad.Predecessors.Add(first);
        a.True(Reaches(), "调用的异常边不算正常分叉");
        first.Statements.Add(new Jump(8, last.Start));
        a.True(Reaches(), "显式跳转可跨块");
        first.Statements[^1] = new Branch(8, Expr.C(1, 1), last.Start, 48);
        a.True(!Reaches(), "即使只有一个记录后继也不跨条件分支");
        first.Statements.RemoveAt(1);
        var other = new Block(48);
        MachineFunction.AddEdge(other, last);
        a.True(!Reaches(), "不跨正常汇合");
        MachineFunction.RemoveEdge(other, last);
        other.Handler = last; other.Successors.Add(last); last.Predecessors.Add(other);
        a.True(Reaches(), "异常前驱不冒充正常前驱");
        last.IsLandingPad = true;
        a.True(!Reaches(), "不进入落地块");
        last.IsLandingPad = false;
        other.Successors.Clear(); other.Handler = null; last.Predecessors.Remove(other);
        MachineFunction.AddEdge(first, other);
        a.True(!Reaches(), "不跨多个正常后继");
        MachineFunction.RemoveEdge(first, other);
        var middle = new Block(12) { Statements = [new Nop(12, "test"), new Jump(12, last.Start)] };
        MachineFunction.RemoveEdge(first, last); MachineFunction.AddEdge(first, middle); MachineFunction.AddEdge(middle, last);
        a.True(Reaches(), "可跨多个直线块");
        middle.Statements.Clear();
        a.True(Reaches(), "元数据读取折叠后的空块仍保持直线控制流");
        last.Statements = [new Jump(24, middle.Start)];
        MachineFunction.AddEdge(last, middle);
        a.True(AllocationPairing.Following(first, 0).Count() < 10, "遇环有限结束");

        var range = new CodeFunction(0, 100, CodeRegion.Managed, BoundaryEvidence.EhFrame)
        {
            ExceptionRegions = [new(0, 12, 80) { ActionOffset = 1 }, new(16, 32, 80) { ActionOffset = 1 }],
        };
        last.Handler = pad;
        string? Problem(params Stmt[] statements) => AllocationPairing.MotionProblem(range, first, allocation, last, constructor, statements, created);
        a.True(Problem() is null, "相同落地点和 action 的分配、构造可合并");
        last.Handler = null;
        a.True(Problem() is not null, "不同异常去向拒绝");
        last.Handler = pad;
        range = range with { ExceptionRegions = [range.ExceptionRegions[0], range.ExceptionRegions[1] with { ActionOffset = 2 }] };
        a.True(Problem() is not null, "相同落地点但 action 不同仍拒绝");
        range = range with { ExceptionRegions = [] }; first.Handler = null; last.Handler = null;
        var temporary = new Variable(Storage.Gpr(1), 1);
        a.True(Problem(new Nop(8, "test"), new Define(8, temporary, Expr.C(3, 64))) is null, "允许无副作用的参数计算");
        a.True(Problem(new Define(8, temporary, new Use(created, 64))) is not null, "构造前复制分配结果拒绝");
        a.True(Problem(new Phi(8, temporary, [created])) is not null, "构造前 phi 使用拒绝");
        foreach (var statement in new Stmt[]
        {
            new Define(8, temporary, new Load(Expr.C(0, 64), 64)),
            new Define(8, temporary, new Intrinsic("unknown", [], 64)),
            new Define(8, temporary, new Unknown("unknown", 64)),
            new Store(8, Expr.C(0, 64), Expr.C(1, 64)),
            new Call(8, CallKind.Direct, Expr.C(300, 64)),
        }) a.True(Problem(statement) is not null, $"不能把分配移动到 {statement.GetType().Name} 之后");
        var slot = new FrameAddress(-8);
        var saved = new Store(8, slot, new Use(temporary, 64));
        var invoker = constructor with { Arguments = [slot] };
        a.True(AllocationPairing.PrivateArgumentStore(saved, invoker, [saved, invoker]), "仅构造调用读取的纯实参写入");
        a.True(!AllocationPairing.PrivateArgumentStore(saved, invoker, [saved, invoker, new Define(28, temporary, new Load(slot, 64))]), "处理器或后续读取使栈槽可观察");
        a.True(!AllocationPairing.PrivateArgumentStore(saved, invoker, [saved, invoker, new Store(28, new Binary(BinOp.Add, slot, Expr.C(4, 64), 64), Expr.C(0, 32))]), "重叠栈写入不能忽略");
        a.True(!AllocationPairing.PrivateArgumentStore(saved, invoker, [saved, invoker, constructor with { Arguments = [slot] }]), "其他调用的地址逃逸不能忽略");
        a.True(!AllocationPairing.PrivateArgumentStore(saved with { Value = new Load(Expr.C(0, 64), 64) }, invoker, [invoker]), "实参写入中的访存仍可抛出");
        return a.Finish("pairing");
    }
}
