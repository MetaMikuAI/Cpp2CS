using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class StackCanaryCheck
{
    [Command("stack-canary", "栈保护守卫的分支方向、支配和逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "normal", "equal", "swapped", "overlap", "escape", "bounded", "unknown", "effect", "bypass", "multiple" })
        {
            var slot = new FrameAddress(-16);
            var thread = new Intrinsic("sysreg_tpidr_el0", [], 64);
            var canary = new Load(new Binary(BinOp.Add, thread, Expr.C(0x28, 64), 64), 64);
            Expr saved = new Load(slot, 64);
            var entry = new Block(0x100) { Statements = [new Store(0x100, slot, canary)] };
            var check = new Block(0x120);
            var done = new Block(0x140) { Statements = [new Return(0x140)] };
            var fail = new Block(0x150) { Statements = [new Call(0x150, CallKind.Direct, Expr.C(0x200, 64))
                { Op = new(OpKind.Import, "__stack_chk_fail") }] };
            var equal = mode == "equal";
            check.Statements.Add(new Branch(0x120, new Compare(equal ? Cond.Eq : Cond.Ne, mode == "swapped" ? saved : canary,
                mode == "swapped" ? canary : saved), equal ? done.Start : fail.Start, equal ? fail.Start : done.Start));
            MachineFunction.AddEdge(entry, check);
            MachineFunction.AddEdge(check, equal ? done : fail);
            MachineFunction.AddEdge(check, equal ? fail : done);
            if (mode == "overlap") entry.Statements.Add(new Store(0x104, new FrameAddress(-12), Expr.C(0, 32)));
            if (mode is "escape" or "bounded" or "unknown") entry.Statements.Add(new Call(0x104, CallKind.Direct, Expr.C(0x300, 64))
                { Arguments = [new FrameAddress(mode == "escape" ? -16 : -32)] });
            if (mode == "effect") fail.Statements.Insert(0, new Store(0x14c, Expr.C(0x400, 64), Expr.C(1, 32)));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x100, 0x154, CodeRegion.Managed, default), Blocks = [entry, check, done, fail] };
            if (mode == "multiple")
            {
                var end = new Block(0x160) { Statements = [new Return(0x160)] };
                done.Statements = [new Branch(0x140, new Compare(Cond.Ne, canary, saved), fail.Start, end.Start)];
                MachineFunction.AddEdge(done, fail);
                MachineFunction.AddEdge(done, end);
                function = new() { Entry = entry.Start, Range = new(0x100, 0x164, CodeRegion.Managed, default), Blocks = [entry, check, done, fail, end] };
            }
            if (mode == "bypass")
            {
                var first = new Block(0x80);
                MachineFunction.AddEdge(first, entry);
                MachineFunction.AddEdge(first, check);
                function = new() { Entry = first.Start, Range = new(0x80, 0x154, CodeRegion.Managed, default), Blocks = [first, entry, check, done, fail] };
            }
            function.Renumber();
            var expected = mode is "normal" or "equal" or "swapped" or "bounded" or "multiple";
            a.Equal(mode == "multiple" ? 2 : expected ? 1 : 0, StackCanaryRecognition.Run(function, extent: (_, _) => mode == "bounded" ? 16 : null), mode);
            if (expected) a.True(check.Statements.Last() is Jump jump && jump.Target == done.Start, "保留正常返回分支");
        }
        return a.Finish("stack-canary");
    }
}
