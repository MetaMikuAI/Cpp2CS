using Cpp2CS.Facts;
using Cpp2CS.Ir;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class DeadFrameStoresCheck
{
    [Command("dead-frame-stores", "无用栈复制的读取、逃逸、回边和异常路径边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "dead", "read", "partial", "branch", "loop", "handler", "escape", "alias", "output", "call", "bound" })
        {
            var saved = new Store(0x104, new FrameAddress(-32), new Use(new(Storage.Gpr(0), 1), 64));
            var read = new Define(0x110, new(Storage.Gpr(1), 1), new Load(new FrameAddress(mode == "partial" ? -29 : -32), mode == "partial" ? 8 : 64));
            var entry = new Block(0x100) { Statements = [saved, new Return(0x108)] };
            var next = new Block(0x110) { Statements = [read, new Return(0x114)] };
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x100, 0x120, CodeRegion.Managed, default), Blocks = [entry] };
            if (mode is "read" or "partial") entry.Statements.Insert(1, read);
            if (mode is "branch" or "loop" or "handler")
            {
                function.Blocks.Add(next);
                MachineFunction.AddEdge(entry, next);
                if (mode == "loop") MachineFunction.AddEdge(next, entry);
                if (mode == "handler") { next.IsLandingPad = true; entry.Handler = next; }
            }
            if (mode is "escape" or "output") entry.Statements.Insert(0, new Call(0x100, CallKind.Direct, Expr.C(0x200, 64)) { Arguments = [new FrameAddress(-32)] });
            if (mode == "alias") entry.Statements.Insert(0, new Define(0x100, new(Storage.Gpr(2), 1),
                new Binary(BinOp.Or, new FrameAddress(-32), Expr.C(0x1000, 64), 64)));
            if (mode == "call") entry.Statements.Insert(1, new Call(0x106, CallKind.Direct, Expr.C(0x200, 64)));
            function.Renumber();
            var removed = DeadFrameStores.Find(function, e => e is FrameAddress f ? f.Offset : null,
                (_, _, _) => mode != "call", (_, _) => 8, (_, _) => mode == "output", mode == "bound" ? new HashSet<Stmt> { saved } : null);
            a.Equal(mode is "dead" or "output", removed.Contains(saved), $"栈复制证明 {mode}");
        }
        return a.Finish("dead-frame-stores");
    }
}
