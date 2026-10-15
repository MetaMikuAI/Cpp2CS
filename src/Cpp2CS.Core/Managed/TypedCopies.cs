using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Managed;

/// <summary>把无间隔副作用、先读完再写回的完整结构体复制恢复为一次值复制，保留读取和写入位置。</summary>
public static class TypedCopies
{
    private sealed record Part(Define Read, Store Write, Expr Source, long SourceOffset, Expr Target, long TargetOffset);

    public static IReadOnlyDictionary<Stmt, ManagedStatement?> Recover(MachineFunction function, ValueRecovery values, ManagedTypes types)
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target);
        var result = new Dictionary<Stmt, ManagedStatement?>();
        foreach (var block in function.Blocks)
        {
            var parts = new List<Part>();
            foreach (var store in block.Statements.OfType<Store>())
            {
                if (store.Value is not Use use || !definitions.TryGetValue(use.Variable, out var define)
                    || define.Value is not Load load || load.Width != use.Width || load.Width % 8 != 0) continue;
                var source = Position(load.Address);
                var target = Position(store.Target);
                parts.Add(new(define, store, source.Base, source.Offset, target.Base, target.Offset));
            }
            foreach (var group in parts.GroupBy(p => (p.Source, p.Target, Delta: p.SourceOffset - p.TargetOffset)))
            {
                var ordered = group.OrderBy(p => p.TargetOffset).ToArray();
                if (ordered.Length < 2 || ordered.Select(p => p.Read).Distinct().Count() != ordered.Length) continue;
                var start = ordered[0].TargetOffset;
                var end = start;
                var contiguous = true;
                foreach (var part in ordered)
                {
                    if (part.TargetOffset != end) { contiguous = false; break; }
                    end += part.Write.Value.Width / 8;
                }
                if (!contiguous || end - start > int.MaxValue / 8) continue;
                var reads = ordered.Select(p => p.Read).ToHashSet();
                var writes = ordered.Select(p => p.Write).ToHashSet();
                var variables = reads.Select(r => r.Target).ToHashSet();
                if (statements.Any(s => s is Phi phi && phi.Sources.Any(variables.Contains)
                    || !(s is Store written && writes.Contains(written)) && ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => variables.Contains(u.Variable)))) continue;
                var firstRead = reads.Min(r => block.Statements.IndexOf(r));
                var lastRead = reads.Max(r => block.Statements.IndexOf(r));
                var firstWrite = writes.Min(w => block.Statements.IndexOf(w));
                var lastWrite = writes.Max(w => block.Statements.IndexOf(w));
                if (firstRead < 0 || lastRead >= firstWrite || block.Statements.Skip(firstRead).Take(lastWrite - firstRead + 1).Any(s =>
                    !(s is Define read && reads.Contains(read)) && !(s is Store written && writes.Contains(written)) && s is not Nop { Text: "hint #0" or "prfm" or "branch to next" })) continue;
                var width = (int)(end - start) * 8;
                if (values.Location(At(group.Key.Source, start + group.Key.Delta), width, out _, whole: true) is not { } source
                    || values.Location(At(group.Key.Target, start), width, out _, whole: true) is not { } target
                    || source.Type != target.Type || types.Kind(source.Type) != ValueKind.Struct) continue;
                var saved = values.Temporary(source.Type);
                foreach (var part in ordered) { result.Add(part.Read, null); result.Add(part.Write, null); }
                var readSite = block.Statements[firstRead];
                var writeSite = block.Statements[firstWrite];
                result[readSite] = new ManagedAssignment(readSite.Address, saved, source);
                result[writeSite] = new ManagedStore(writeSite.Address, target, saved);
            }
        }
        return result;
    }

    private static (Expr Base, long Offset) Position(Expr expression) => expression switch
    {
        FrameAddress frame => (new FrameAddress(0), frame.Offset),
        Binary { Op: BinOp.Add, Right: Const c } add => (add.Left, c.Signed),
        _ => (expression, 0),
    };
    private static Expr At(Expr address, long offset) => address is FrameAddress frame ? new FrameAddress(frame.Offset + offset)
        : offset == 0 ? address : new Binary(BinOp.Add, address, Expr.C(unchecked((ulong)offset), 64), 64);
}
