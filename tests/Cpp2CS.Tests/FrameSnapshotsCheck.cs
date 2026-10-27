using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FrameSnapshotsCheck
{
    [Command("frame-snapshots", "帧片段快照的支配、逃逸和重叠边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "snapshot", "overlap", "rewrite", "escape", "early", "bypass" })
        {
            var frame = new FrameAddress(-64);
            var saved = new Use(new Variable(Storage.Vec(0), 1), 128);
            var store = new Store(0x100, frame, saved);
            var read = new Define(0x120, new Variable(Storage.Vec(1), 1), new Load(frame, 128));
            var entry = new Block(0x80) { Statements = [new Define(0x80, saved.Variable, new Load(Expr.C(0x2000, 64), 128))] };
            var write = new Block(0x100) { Statements = [store] };
            var done = new Block(0x120) { Statements = [read] };
            MachineFunction.AddEdge(entry, write);
            MachineFunction.AddEdge(write, done);
            if (mode == "overlap") write.Statements.Add(new Store(0x104, new FrameAddress(-56), Expr.C(1, 64)));
            if (mode == "rewrite") write.Statements.Add(new Store(0x104, frame, saved));
            if (mode == "escape") write.Statements.Add(new Call(0x104, CallKind.Direct, Expr.C(0x3000, 64)) { Arguments = [new FrameAddress(-80)] });
            if (mode == "early") entry.Statements.Add(new Define(0x84, new Variable(Storage.Vec(2), 1), new Load(frame, 128)));
            if (mode == "bypass") MachineFunction.AddEdge(entry, done);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x80, 0x128, CodeRegion.Managed, default), Blocks = [entry, write, done] };
            function.Renumber();
            var changes = FrameSnapshots.Read(function);
            a.Equal(mode == "snapshot" ? 2 : 0, changes.Count, mode);
            if (mode == "snapshot")
                a.True(changes[store] is Nop && changes[read] is Define replacement && ReferenceEquals(replacement.Value, saved), "使用原寄存器快照，不再次读取原地址");
        }
        return a.Finish("frame-snapshots");
    }
}
