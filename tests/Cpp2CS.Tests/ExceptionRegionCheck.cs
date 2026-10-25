using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ExceptionRegionCheck
{
    [Command("eh-regions", "手写图的语句边界、闭包与嵌套正反例", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        Call Op(ulong at, OpKind op) => new(at, CallKind.Direct, Expr.C(0, 64)) { Op = new(op, null) };
        Block Block(ulong at, params Stmt[] statements) => new(at) { End = at + 0x10, Statements = [.. statements] };
        void Exception(Block from, Block to) { MachineFunction.AddEdge(from, to); from.Handler = to; to.IsLandingPad = true; }
        MachineFunction Function(Block entry, params Block[] others)
        {
            var f = new MachineFunction { Entry = entry.Start, Range = new(entry.Start, 0x2000, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, .. others] };
            f.Renumber(); return f;
        }
        var source = Block(0x1000, new Define(0x1000, new(Storage.Gpr(2), 1), Expr.C(9, 64)), Op(0x1004, OpKind.CallVirtual));
        var handler = Block(0x1100, Op(0x1100, OpKind.BeginCatch), Op(0x1104, OpKind.EndCatch), new Store(0x1108, Expr.C(0x8888, 64), Expr.C(1, 64)), new Jump(0x110c, 0x1200));
        var done = Block(0x1200, new Return(0x1200));
        MachineFunction.AddEdge(source, done); MachineFunction.AddEdge(handler, done); Exception(source, handler);
        var function = Function(source, handler, done);
        var layout = ExceptionRegionBuilder.Build(function, _ => true);
        a.True(layout.Succeeded, $"基本 catch 构造：{layout.Reason} {layout.Detail}");
        a.Equal(1, layout.Regions.Length, "一个 catch 区域");
        a.True(layout.Regions.Single().Handler.SelectMany(f => f.Statements).All(s => s is not Store), "EndCatch 后的同块写入在 handler 外");
        a.True(layout.Order[0].Block == source && layout.Order[0].First == 0, "整个方法从原入口片段开始");
        a.Equal(4, handler.Statements.Count, "区域视图不修改生产块");

        // 有调用的连接语句不能因两端受相同 handler 保护就扩大捕获范围。
        var first = Block(0x1300, Op(0x1300, OpKind.CallVirtual));
        var gap = Block(0x1320, Op(0x1320, OpKind.CallInterface));
        var second = Block(0x1340, Op(0x1340, OpKind.CallVirtual));
        var catch2 = Block(0x1380, Op(0x1380, OpKind.BeginCatch), Op(0x1384, OpKind.EndCatch));
        var end2 = Block(0x13a0, new Return(0x13a0));
        MachineFunction.AddEdge(first, gap); MachineFunction.AddEdge(gap, second); MachineFunction.AddEdge(second, end2); MachineFunction.AddEdge(catch2, end2);
        Exception(first, catch2); Exception(second, catch2);
        var joined = Function(first, gap, second, catch2, end2);
        var rejected = ExceptionRegionBuilder.Build(joined, _ => true);
        a.Equal("未证成/连接语句可能抛出", rejected.Reason, "不能把未受保护的调用加入 try");
        gap.Statements[0] = new Store(0x1320, Expr.C(0x8888, 64), Expr.C(2, 64));
        var connected = ExceptionRegionBuilder.Build(joined, _ => true);
        a.True(connected.Succeeded && connected.Regions[0].Try.Any(f => f.Block == gap), "非抛出连接语句构造单入口闭包");

        var faultSource = Block(0x1400, Op(0x1400, OpKind.CallVirtual));
        var cleanup = Block(0x1440, Op(0x1440, OpKind.EndCatch), new Store(0x1444, Expr.C(0x8888, 64), Expr.C(3, 64)), Op(0x1448, OpKind.ResumeUnwind));
        var end3 = Block(0x1480, new Return(0x1480));
        MachineFunction.AddEdge(faultSource, end3); Exception(faultSource, cleanup);
        var fault = ExceptionRegionBuilder.Build(Function(faultSource, cleanup, end3), _ => true);
        a.True(fault.Succeeded && fault.Regions.Single().Kind == "fault", "cleanup 的可见写入保留为 fault 候选");
        cleanup.Statements.RemoveAt(1);
        var bookkeeping = ExceptionRegionBuilder.Build(Function(faultSource, cleanup, end3), _ => true);
        a.Equal("未证成/只有清理", bookkeeping.Reason, "纯 EndCatch/Resume 不伪造托管 catch");

        var outerFirst = Block(0x1500, Op(0x1500, OpKind.CallVirtual));
        var innerCall = Block(0x1520, Op(0x1520, OpKind.CallVirtual));
        var outerLast = Block(0x1540, Op(0x1540, OpKind.CallVirtual));
        var innerCatch = Block(0x1580, Op(0x1580, OpKind.BeginCatch), Op(0x1584, OpKind.EndCatch));
        var outerCatch = Block(0x15a0, Op(0x15a0, OpKind.BeginCatch), Op(0x15a4, OpKind.EndCatch));
        var end4 = Block(0x15c0, new Return(0x15c0));
        MachineFunction.AddEdge(outerFirst, innerCall); MachineFunction.AddEdge(innerCall, outerLast);
        MachineFunction.AddEdge(innerCatch, outerLast); MachineFunction.AddEdge(outerLast, end4); MachineFunction.AddEdge(outerCatch, end4);
        Exception(outerFirst, outerCatch); Exception(outerLast, outerCatch); Exception(innerCall, innerCatch);
        var nestedFunction = Function(outerFirst, innerCall, outerLast, innerCatch, outerCatch, end4);
        var nested = ExceptionRegionBuilder.Build(nestedFunction, _ => true);
        a.True(nested.Succeeded && nested.Regions.Count(r => r.Parent is not null) == 1, $"内层完整 try+handler 嵌入外层 try：{nested.Reason} {nested.Detail}");
        innerCatch.Statements.Insert(1, Op(0x1582, OpKind.CallInterface));
        var unsafeNested = ExceptionRegionBuilder.Build(nestedFunction, _ => true);
        a.True(!unsafeNested.Succeeded, "不能使内层 handler 中原本向外逃逸的调用改被外层捕获");

        // 同一门既有 wrapper 也有 catch-all 来源时，不能把 selector 无条件置为 1。
        var selectorValue = new Variable(Storage.Gpr(1), 1);
        var gate = Block(0x1680, new Define(0x1680, selectorValue, new Intrinsic("eh_selector", [], 64)),
            new Branch(0x1684, new Compare(Cond.Eq, new Use(selectorValue, 64), Expr.C(1, 64)), 0x16a0, 0x16c0));
        var typed = Block(0x16a0, Op(0x16a0, OpKind.BeginCatch), Op(0x16a4, OpKind.EndCatch));
        var terminate = Block(0x16c0, Op(0x16c0, OpKind.Terminate));
        var start = Block(0x1600, Op(0x1600, OpKind.CallVirtual));
        var end5 = Block(0x16e0, new Return(0x16e0));
        MachineFunction.AddEdge(start, end5); Exception(start, gate);
        MachineFunction.AddEdge(gate, typed); MachineFunction.AddEdge(gate, terminate); MachineFunction.AddEdge(typed, end5);
        var selectorFunction = Function(start, gate, typed, terminate, end5);
        var range = selectorFunction.Range with { ExceptionRegions = [
            new(0x1600, 0x1604, 0x1680) { ActionOffset = 1, Actions = [new(1, 1, 0, 123, "typed-catch")] },
            new(0x1610, 0x1614, 0x1670) { ActionOffset = 3, Actions = [new(3, 2, 0, 0, "catch-all")] }] };
        selectorFunction = new() { Entry = start.Start, Range = range, Blocks = selectorFunction.Blocks };
        var mixed = ExceptionRegionBuilder.Build(selectorFunction, _ => true, at => at == 0x1670 ? 0x1680UL : null);
        a.True(!mixed.Succeeded, "保留来自已删除空桥的 catch-all selector，不能误剪 Terminate");
        range = range with { ExceptionRegions = [range.ExceptionRegions[0]] };
        selectorFunction = new() { Entry = start.Start, Range = range, Blocks = selectorFunction.Blocks };
        a.True(ExceptionRegionBuilder.Build(selectorFunction, _ => true).Succeeded, "全部来源为 wrapper 时才剪 selector 门");
        FrameInitializationCheck.Run(a);
        return a.Finish("eh-regions");
    }
}
