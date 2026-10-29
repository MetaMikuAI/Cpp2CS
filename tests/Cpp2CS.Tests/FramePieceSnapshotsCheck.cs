using System.Numerics;
using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery;

namespace Cpp2CS.Tests;

internal static class FramePieceSnapshotsCheck
{
    [Command("frame-piece-snapshots", "跨片栈读取的字节、支配与逃逸边界", Gate = Gate.Unit)]
    public static int Run()
    {
        var a = new Assertions();
        foreach (var mode in new[] { "pieces", "reverse", "safe-call", "early", "bypass", "rewrite", "escape", "hidden", "gap", "interrupted", "handler", "overread" })
        {
            var first = new Use(new Variable(Storage.Vec(0), 0), 128);
            var second = new Use(new Variable(Storage.Vec(1), 0), 128);
            var low = new Store(0x110, new FrameAddress(-128), first);
            var high = new Store(0x114, new FrameAddress(mode == "gap" ? -108 : -112), second);
            var entry = new Block(0x100);
            var write = new Block(0x110) { Statements = mode == "reverse" ? [high, low] : [low, high] };
            var read = new Define(0x120, new Variable(Storage.Vec(2), 1), new Load(new FrameAddress(mode == "overread" ? -104 : -116), 128));
            var done = new Block(0x120) { Statements = [read] };
            MachineFunction.AddEdge(entry, write);
            MachineFunction.AddEdge(write, done);
            if (mode == "early") entry.Statements.Add(new Define(0x100, new(Storage.Gpr(0), 1), new Load(new FrameAddress(-128), 64)));
            if (mode == "bypass") MachineFunction.AddEdge(entry, done);
            if (mode == "rewrite") done.Statements.Insert(0, new Store(0x118, new FrameAddress(-120), Expr.C(4, 32)));
            if (mode is "escape" or "hidden" or "safe-call") entry.Statements.Add(new Call(0x104, CallKind.Direct, Expr.C(0x200, 64))
                { Arguments = mode == "escape" ? [new FrameAddress(-144)] : [] });
            if (mode == "interrupted") write.Statements.Insert(1, new Call(0x112, CallKind.Direct, Expr.C(0x200, 64)));
            var function = new MachineFunction { Entry = entry.Start, Range = new(0x100, 0x124, CodeRegion.Managed, default)
                { ExceptionRegions = mode == "handler" ? [new(0x100, 0x124, 0x140)] : [] }, Blocks = [entry, write, done] };
            function.Renumber();
            var changes = FramePieceSnapshots.Read(function, (_, _, _) => mode != "hidden", e => e is FrameAddress f ? f.Offset : null);
            var accepted = mode is "pieces" or "reverse" or "safe-call";
            a.Equal(accepted ? 3 : 0, changes.Count, mode);
            if (!accepted) continue;
            a.True(changes[low] is Nop && changes[high] is Nop, "两处备份的全部读取已有替换");
            BigInteger Value(Expr expression) => expression switch
            {
                Const c => c.Value,
                Use u => new BigInteger(Enumerable.Range(u.Variable == first.Variable ? 1 : 17, 16).Select(i => (byte)i).ToArray(), isUnsigned: true),
                Extract e => (Value(e.Operand) >> e.Low) & ((BigInteger.One << e.Width) - 1),
                Insert insert => (Value(insert.Base) & ~(((BigInteger.One << insert.Value.Width) - 1) << insert.Low))
                    | ((Value(insert.Value) & ((BigInteger.One << insert.Value.Width) - 1)) << insert.Low),
                _ => throw new InvalidOperationException(expression.ToString()),
            };
            var recovered = ((Define)changes[read]).Value;
            a.Equal(new BigInteger(Enumerable.Range(13, 16).Select(i => (byte)i).ToArray(), isUnsigned: true), Value(recovered), "跨片 16 字节与原内存一致");
            a.True(!ExprMap.Walk(recovered).OfType<Load>().Any(), "只使用原 SSA 快照，不重读来源");
        }
        return a.Finish("frame-piece-snapshots");
    }
}
