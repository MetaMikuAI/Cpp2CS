using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;
using Cpp2CS.Machine.Ssa;

namespace Cpp2CS.Tests;

internal static class OutlinedCallCheck
{
    [Command("outlined-calls", "原生闭包展开与异常边复制", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var input = new Variable(Storage.Gpr(0), 0);
        var output = new Variable(Storage.Gpr(0), 1);
        (MachineFunction Caller, Block Block, Call Call, Block Handler) Caller(bool used = false)
        {
            var call = new Call(0x1004, CallKind.Direct, Expr.C(0x2000, 64))
                { Arguments = [new FrameAddress(-16)], Sources = [Storage.Gpr(0)], Defines = [output], Results = [Storage.Gpr(0)] };
            var block = new Block(0x1000) { Statements = [call], End = 0x1008 };
            var done = new Block(0x1008) { Statements = [new Return(0x1008) { Value = used ? new Use(output, 64) : null }] };
            var handler = new Block(0x1010) { IsLandingPad = true, Statements = [
                new Phi(0x1010, new Variable(Storage.Gpr(19), 1), [new Variable(Storage.Gpr(19), 0)]), new Return(0x1014)] };
            MachineFunction.AddEdge(block, done);
            MachineFunction.AddEdge(block, handler); block.Handler = handler;
            return (new() { Entry = block.Start, Range = new(0x1000, 0x1020, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [block, done, handler] }, block, call, handler);
        }
        MachineFunction Callee(bool local = false)
        {
            var entry = new Block(0x2000) { Statements = [new Branch(0x2000,
                new Compare(Cond.Eq, new Load(new Use(input, 64), 32), Expr.C(0, 32)), 0x2004, 0x200c)] };
            var first = new Block(0x2004) { Statements = [new Call(0x2004, CallKind.Direct, Expr.C(0x3000, 64)), new Return(0x2008)] };
            var second = new Block(0x200c) { Statements = [new Call(0x200c, CallKind.Direct, Expr.C(0x4000, 64)), new Return(0x2010)] };
            if (local) first.Statements.Insert(0, new Store(0x2004, new FrameAddress(-8), Expr.C(1, 64)));
            MachineFunction.AddEdge(entry, first); MachineFunction.AddEdge(entry, second);
            return new() { Entry = entry.Start, Range = new(0x2000, 0x2014, CodeRegion.Runtime, BoundaryEvidence.EhFrame), Blocks = [entry, first, second] };
        }
        var sample = Caller();
        var helper = Callee();
        helper.EntryBlock.Statements.Insert(0, new Nop(0x2000, "类布局已初始化"));
        var before = helper.ToString();
        a.True(OutlinedCallInlining.Run(sample.Caller, sample.Block, sample.Call, helper), "展开两个返回分支");
        a.Equal(2, sample.Handler.Predecessors.Count, "每个内部调用继承异常边");
        a.True(sample.Handler.Statements[0] is Phi { Sources.Length: 2 } phi && phi.Sources.All(v => v == new Variable(Storage.Gpr(19), 0)), "异常 phi 保留调用点输入");
        a.True(sample.Caller.Blocks.SelectMany(b => b.Statements).OfType<Call>().All(c => c.NativeExceptionSite == sample.Call.Address), "内部调用保留原始 LSDA 位置");
        a.Equal(0, SsaCheck.Verify(sample.Caller, Dominators.Compute(sample.Caller)).Count, "展开后 SSA 完整");
        a.Equal(before, helper.ToString(), "展开不修改共享的被调函数");
        a.True(sample.Caller.Blocks.SelectMany(b => b.Statements).All(s => !helper.Blocks.SelectMany(b => b.Statements).Any(original => ReferenceEquals(s, original))),
            "包含 Nop 在内的语句都使用独立实例，重复展开不会共享位置键");
        var usedResult = Caller(true);
        a.True(!OutlinedCallInlining.Run(usedResult.Caller, usedResult.Block, usedResult.Call, Callee()), "返回值被使用时拒绝无返回展开");
        var returned = Caller(true);
        var valueHelper = Callee();
        foreach (var b in valueHelper.Blocks.Where(b => b.Statements.Last() is Return))
            b.Statements[^1] = new Return(b.Statements[^1].Address) { Value = Expr.C(b.Start, 64) };
        a.True(OutlinedCallInlining.Run(returned.Caller, returned.Block, returned.Call, valueHelper), "各返回分支传回标量结果");
        a.Equal(0, SsaCheck.Verify(returned.Caller, Dominators.Compute(returned.Caller)).Count, "返回值合流后 SSA 完整");
        a.True(returned.Caller.Blocks.SelectMany(b => b.Statements).OfType<Phi>().Any(p => p.Target == output && p.Sources.Length == 2), "调用输出由两个实际返回值合流");
        var middle = Caller(true);
        MachineFunction.RemoveEdge(middle.Block, middle.Handler);
        middle.Block.Handler = null;
        middle.Block.Statements.Add(new Define(0x1006, new Variable(Storage.Gpr(2), 1), new Use(output, 64)));
        a.True(OutlinedCallInlining.Run(middle.Caller, middle.Block, middle.Call, valueHelper), "普通基本块中间的调用也能展开");
        a.Equal(0, SsaCheck.Verify(middle.Caller, Dominators.Compute(middle.Caller)).Count, "拆开基本块后保持返回值支配使用");
        var locals = Caller();
        a.True(!OutlinedCallInlining.Run(locals.Caller, locals.Block, locals.Call, Callee(true)), "存在独立栈局部时保留原调用");
        return a.Finish("outlined-calls");
    }
}
