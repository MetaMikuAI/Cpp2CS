using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameWritebacksCheck
{
    [Command("frame-writebacks", "重叠栈快照写回的合流、修改和调用边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "normal", "source-write", "spill-write", "call", "alias-write", "bypass", "loop" })
        {
            var entry = new Block(0x100);
            var changed = new Block(0x120);
            var unchanged = new Block(0x130);
            var done = new Block(0x140);
            for (var i = 0; i < 2; i++)
            {
                var value = new Variable(Storage.Vec(i), 1);
                entry.Statements.Add(new Define((ulong)(0x100 + i * 8), value, new Load(new FrameAddress(-128 + i * 15), 128)));
                entry.Statements.Add(new Store((ulong)(0x104 + i * 8), new FrameAddress(-64 + i * 15), new Use(value, 128)));
                var restored = new Variable(Storage.Vec(i + 2), 1);
                done.Statements.Add(new Define((ulong)(0x140 + i * 8), restored, new Load(new FrameAddress(-64 + i * 15), 128)));
                done.Statements.Add(new Store((ulong)(0x144 + i * 8), new FrameAddress(-128 + i * 15), new Use(restored, 128)));
            }
            if (mode is "source-write" or "spill-write") changed.Statements.Add(new Store(0x120,
                new FrameAddress(mode == "source-write" ? -113 : -49), Expr.C(7, 8)));
            if (mode == "call") changed.Statements.Add(new Call(0x120, CallKind.Direct, Expr.C(0x300, 64)));
            if (mode == "alias-write") changed.Statements.Add(new Store(0x120, new Use(new Variable(Storage.Gpr(0), 0), 64), Expr.C(7, 8)));
            MachineFunction.AddEdge(entry, changed);
            MachineFunction.AddEdge(entry, unchanged);
            MachineFunction.AddEdge(changed, done);
            MachineFunction.AddEdge(unchanged, done);
            var first = new Block(0x80);
            MachineFunction.AddEdge(first, entry);
            if (mode == "bypass") MachineFunction.AddEdge(first, done);
            if (mode == "loop") MachineFunction.AddEdge(done, entry);
            var function = new MachineFunction { Entry = first.Start, Range = new(0x80, 0x154, CodeRegion.Managed, default), Blocks = [first, entry, changed, unchanged, done] };
            function.Renumber();
            a.Equal(mode is "normal" or "loop" ? 2 : mode is "source-write" or "spill-write" ? 1 : 0, FrameWritebacks.Run(function), mode);
        }
        foreach (var mode in new[] { "dead", "caller", "crossing", "read", "escape", "call", "bounded", "unknown" })
        {
            var offset = mode == "caller" ? 0 : mode == "crossing" ? -8 : -64;
            var store = new Store(0x100, new FrameAddress(offset), new Use(new Variable(Storage.Vec(0), 1), 128));
            var statements = new List<Stmt> { store };
            if (mode == "read") statements.Add(new Define(0x104, new(Storage.Gpr(0), 1), new Load(new FrameAddress(-60), 32)));
            if (mode == "escape") statements.Add(new Store(0x104, Expr.C(0x400, 64), new FrameAddress(-80)));
            if (mode is "call" or "bounded" or "unknown") statements.Add(new Call(0x104, CallKind.Direct, Expr.C(0x300, 64))
                { Arguments = mode == "call" ? [] : [new FrameAddress(-80)] });
            a.Equal(mode is "dead" or "bounded", FrameWritebacks.Unread(statements, store, (_, _) => mode == "bounded" ? 16 : null,
                (_, _, _) => mode != "call"), "未读取写入 " + mode);
        }
        return a.Finish("frame-writebacks");
    }
}
