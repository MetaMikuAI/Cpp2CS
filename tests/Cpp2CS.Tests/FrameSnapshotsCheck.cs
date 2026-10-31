using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
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
        foreach (var mode in new[] { "equal", "different", "changed-source", "partial", "escape-tail", "bypass" })
        {
            var first = new Variable(Storage.Vec(0), 1);
            var second = new Variable(Storage.Vec(1), 1);
            var entry = new Block(0x1000) { Statements = [new Define(0x1000, first, new Load(new FrameAddress(-64), 128))] };
            if (mode == "changed-source") entry.Statements.Add(new Store(0x1004, new FrameAddress(-52), Expr.C(9, 32)));
            entry.Statements.Add(new Define(0x1008, second, new Load(new FrameAddress(mode == "different" ? -48 : -52), 128)));
            var firstStore = new Store(0x1010, new FrameAddress(-128), new Use(first, 128));
            var secondStore = new Store(0x1014, new FrameAddress(-116), new Use(second, 128));
            entry.Statements.Add(firstStore);
            var write = new Block(0x1014) { Statements = [secondStore] };
            var done = new Block(0x1020) { Statements = [
                new Define(0x1020, new(Storage.Vec(2), 1), new Load(new FrameAddress(-128), 128)),
                new Define(0x1024, new(Storage.Vec(3), 1), new Load(new FrameAddress(-116), 128))] };
            if (mode == "partial") done.Statements.Add(new Define(0x1028, new(Storage.Gpr(0), 1), new Load(new FrameAddress(-104), 32)));
            if (mode == "escape-tail") write.Statements.Add(new Call(0x1018, CallKind.Direct, Expr.C(0x3000, 64)) { Arguments = [new FrameAddress(-104)] });
            MachineFunction.AddEdge(entry, write);
            MachineFunction.AddEdge(write, done);
            if (mode == "bypass") MachineFunction.AddEdge(entry, done);
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x1000, 0x1030, CodeRegion.Managed, default), Blocks = [entry, write, done] };
            function.Renumber();
            var changes = FrameSnapshots.Read(function);
            a.Equal(mode == "equal" ? 4 : 0, changes.Count, $"重叠快照 {mode}");
        }
        foreach (var mode in new[] { "branches", "joined", "early", "partial", "escape", "call", "safe-call", "handler", "dead", "dead-call", "dead-escape", "dead-object-read" })
        {
            var slot = new FrameAddress(-96);
            var first = new Use(new Variable(Storage.Vec(0), 1), 128);
            var second = new Use(new Variable(Storage.Vec(0), 2), 128);
            var entry = new Block(0x2000);
            var left = new Block(0x2010) { Statements = [new Store(0x2010, slot, first)] };
            var right = new Block(0x2020) { Statements = [new Store(0x2020, slot, second)] };
            var leftRead = new Define(0x2030, new(Storage.Vec(1), 1), new Load(slot, 128));
            var rightRead = new Define(0x2040, new(Storage.Vec(1), 2), new Load(slot, 128));
            var leftUse = new Block(0x2030) { Statements = [leftRead] };
            var rightUse = new Block(0x2040) { Statements = [rightRead] };
            MachineFunction.AddEdge(entry, left); MachineFunction.AddEdge(entry, right);
            MachineFunction.AddEdge(left, leftUse); MachineFunction.AddEdge(right, rightUse);
            if (mode == "joined") MachineFunction.AddEdge(right, leftUse);
            if (mode == "early") entry.Statements.Add(leftRead);
            if (mode == "partial") left.Statements.Add(new Store(0x2014, new FrameAddress(-88), Expr.C(0, 64)));
            if (mode is "escape" or "call" or "safe-call" or "dead-call" or "dead-escape") left.Statements.Add(new Call(0x2018, CallKind.Direct, Expr.C(0x3000, 64))
                { Arguments = mode.EndsWith("escape", StringComparison.Ordinal) ? [slot] : [] });
            if (mode.StartsWith("dead", StringComparison.Ordinal))
            {
                leftUse.Statements.Clear(); rightUse.Statements.Clear();
                entry.Statements.Add(new Define(0x2000, first.Variable, new Load(mode == "dead-object-read" ? new Use(new(Storage.Gpr(0), 0), 64) : new FrameAddress(-32), 128)));
                entry.Statements.Add(new Define(0x2004, second.Variable, new Load(new FrameAddress(-16), 128)));
            }
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x2000, 0x2050, CodeRegion.Managed, default)
                { ExceptionRegions = mode == "handler" ? [new(0x2000, 0x2044, 0x2060)] : [] }, Blocks = [entry, left, right, leftUse, rightUse] };
            var changes = FrameBranchSnapshots.Read(function, (_, _, _) => mode is not ("call" or "dead-call"));
            a.Equal(mode is "branches" or "safe-call" ? 4 : mode == "dead" ? 2 : 0, changes.Count, $"分支快照 {mode}");
            if (mode == "branches")
                a.True(changes[leftRead] is Define { Value: Use l } && l == first
                    && changes[rightRead] is Define { Value: Use r } && r == second, "分支分别使用到达该读取的原快照");
        }
        foreach (var mode in new[] { "mixed", "wide-read", "overlap", "uninitialized", "phi" })
        {
            var slot = new FrameAddress(-80);
            var input = new Use(new Variable(Storage.Vec(0), 0), 64);
            var vector = new Use(new Variable(Storage.Vec(2), 1), 128);
            var first = new Variable(Storage.Vec(1), 1);
            var second = new Variable(Storage.Vec(3), 1);
            var initialStore = new Store(0x3000, slot, input);
            var firstRead = new Define(0x3010, first, new Load(slot, 128));
            var vectorStore = new Store(0x3020, slot, vector);
            var secondRead = new Define(0x3030, second, new Load(slot, 128));
            var entry = new Block(0x3000) { Statements = [initialStore] };
            var read = new Block(0x3010) { Statements = [firstRead,
                new Define(0x3014, new(Storage.Vec(4), 1), new Use(first, mode == "wide-read" ? 128 : 32))] };
            var later = new Block(0x3020) { Statements = [vectorStore, secondRead,
                new Define(0x3034, new(Storage.Vec(5), 1), new Extract(new Use(second, 128), 32, 32))] };
            MachineFunction.AddEdge(entry, read); MachineFunction.AddEdge(read, later);
            if (mode == "uninitialized") entry.Statements.Clear();
            if (mode == "overlap") read.Statements.Add(new Store(0x3018, new FrameAddress(-76), Expr.C(0, 32)));
            if (mode == "phi") later.Statements.Add(new Phi(0x3038, new(Storage.Vec(6), 1), [first]));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x3000, 0x3040, CodeRegion.Managed, default), Blocks = [entry, read, later] };
            var changes = FrameBranchSnapshots.Read(function, (_, _, _) => true);
            a.Equal(mode == "mixed" ? 4 : 0, changes.Count, $"栈槽不同宽度的生命期 {mode}");
            if (mode == "mixed")
                a.True(changes[firstRead] is Define { Value: Use low } && low.Variable == input.Variable && low.Width == 32
                    && changes[secondRead] is Define { Value: Use full } && full == vector,
                    "标量只恢复有证据的低位，后续向量仍保留完整快照");
        }
        foreach (var mode in new[] { "reuse", "escape", "bypass", "partial-read" })
        {
            var slot = new FrameAddress(-80);
            var value = new Use(new(Storage.Vec(0), 1), 64);
            var store = new Store(0x4000, slot, value);
            var read = new Define(0x4010, new(Storage.Vec(1), 1), new Load(slot, 64));
            var entry = new Block(0x3ff0);
            var initial = new Block(0x4000) { Statements = [store] };
            var use = new Block(0x4010) { Statements = [read, new Store(0x4014, slot, Expr.C(7, 32)),
                new Call(0x4018, CallKind.Direct, Expr.C(0x5000, 64)) { Arguments = [slot] }] };
            MachineFunction.AddEdge(entry, initial); MachineFunction.AddEdge(initial, use);
            if (mode == "escape") initial.Statements.Add(new Call(0x4004, CallKind.Direct, Expr.C(0x5000, 64)) { Arguments = [slot] });
            if (mode == "bypass") MachineFunction.AddEdge(entry, use);
            if (mode == "partial-read") use.Statements.Add(new Define(0x401c, new(Storage.Vec(2), 1), new Load(slot, 64)));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x3ff0, 0x4020, CodeRegion.Managed, default), Blocks = [entry, initial, use] };
            function.Renumber();
            var changes = FrameLifetimeSnapshots.Read(function, (_, _, _) => true, (_, _) => 4, e => (e as FrameAddress)?.Offset);
            a.Equal(mode == "reuse" ? 2 : 0, changes.Count, $"局部快照与后续装箱生命期 {mode}");
        }
        return a.Finish("frame-snapshots");
    }
}
