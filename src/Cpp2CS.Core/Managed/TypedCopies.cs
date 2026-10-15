using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Managed;

/// <summary>把无间隔副作用、先读完再写回的完整结构体复制恢复为一次值复制，保留读取和写入位置。</summary>
public static class TypedCopies
{
    private sealed record Part(Define Read, Store Write, Expr Source, long SourceOffset, Expr Target, long TargetOffset);

    public static IReadOnlyDictionary<Stmt, ManagedStatement?> Recover(MachineFunction function, ValueRecovery values, ManagedTypes types, TypeRef returnType)
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target);
        var result = new Dictionary<Stmt, ManagedStatement?>();
        foreach (var block in function.Blocks)
        {
            if (block.Statements.LastOrDefault() is Return { Value: { } returned, Pieces.Length: 0, Buffer: null } ret && types.Kind(returnType) == ValueKind.Struct)
            {
                var width = types.Size(returnType) * 8;
                var reads = new List<Define>();
                var variables = new HashSet<Variable>();
                Expr? Origin(Expr expression)
                {
                    if (width is not (8 or 16 or 32 or 64) || expression.Width < width) return null;
                    if (expression is Ir.Convert { Kind: ConvKind.Bitcast or ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion)
                        return Origin(conversion.Operand);
                    if (expression is not Use use) return expression;
                    if (!variables.Add(use.Variable) || !definitions.TryGetValue(use.Variable, out var define)
                        || !block.Statements.Contains(define)) return null;
                    reads.Add(define);
                    return Origin(define.Value);
                }
                if (Origin(returned) is Load load && load.Width == width && reads.Count > 0
                    && reads.Zip(reads.Skip(1)).All(p => block.Statements.IndexOf(p.First) > block.Statements.IndexOf(p.Second))
                    && !statements.Any(s => s is Phi phi && phi.Sources.Any(variables.Contains)
                        || s != ret && !(s is Define define && reads.Contains(define))
                        && ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => variables.Contains(u.Variable)))
                    && values.Location(load.Address, width, out _, whole: true) is { } source && source.Type == returnType)
                {
                    var saved = values.Temporary(returnType);
                    foreach (var read in reads) result.Add(read, null);
                    result[reads[^1]] = new ManagedAssignment(reads[^1].Address, saved, source);
                    result.Add(ret, new ManagedReturn(ret.Address, saved));
                }
            }
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
