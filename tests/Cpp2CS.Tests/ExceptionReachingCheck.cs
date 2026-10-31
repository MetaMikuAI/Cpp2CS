using Cpp2CS.Facts;
using Cpp2CS.Image;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class ExceptionReachingCheck
{
    [Command("exception-reaching", "异常前寄存器来源的回边与覆盖边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        var storage = Storage.Gpr(24);
        var first = new Variable(storage, 1);
        var next = new Variable(storage, 2);
        var entry = new Block(0) { End = 8, Statements = [new Define(0, first, Expr.C(1, 64)), new Jump(4, 8)] };
        var loop = new Block(8) { End = 16, Statements = [new Jump(12, 8)] };
        MachineFunction.AddEdge(entry, loop); MachineFunction.AddEdge(loop, loop);
        var function = new MachineFunction { Entry = 0, Range = new(0, 16, CodeRegion.Managed, BoundaryEvidence.EhFrame), Blocks = [entry, loop] };
        function.Renumber();
        Variable[] Sources(Block block, int end) => ExceptionsRules.ExceptionReachingDefinitions(function, block, end, end < block.Statements.Count ? block.Statements[end].Address : ulong.MaxValue, storage);
        a.True(Sources(loop, 0).SequenceEqual([first]), "不写寄存器的回边保留入环值");
        loop.Statements.Insert(0, new Define(8, next, Expr.C(2, 64)));
        a.True(Sources(loop, 0).ToHashSet().SetEquals([first, next]), "上轮写入与首次进入不同，保留两个来源");
        a.True(Sources(loop, 1).SequenceEqual([next]), "本轮写入之后只取新值");
        loop.Statements[0] = new Phi(8, next, [first, next]);
        a.True(Sources(loop, 1).SequenceEqual([next]), "已存在的 SSA 汇合直接提供当前值");
        entry.Statements[0] = new Call(0, CallKind.Direct, Expr.C(32, 64)) { Results = [storage], Defines = [first] };
        a.True(Sources(entry, 0).SequenceEqual([new Variable(storage, 0)]), "调用抛出前不能读取其返回值");
        a.True(Sources(entry, 1).SequenceEqual([first]), "正常调用返回后可以读取结果");
        entry.Statements.Clear(); loop.Statements.Clear();
        a.True(Sources(loop, 0).SequenceEqual([new Variable(storage, 0)]), "缺少写入仍保留未初始化入口值，不猜零");
        return a.Finish("exception-reaching");
    }
}
