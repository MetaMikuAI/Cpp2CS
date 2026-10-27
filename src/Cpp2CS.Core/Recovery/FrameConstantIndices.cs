using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>以各路径到达的栈写入证明常量下标，使固定帧地址可以继续参与栈槽提升。</summary>
internal static class FrameConstantIndices
{
    internal static int Run(MachineFunction function)
    {
        var positions = function.Blocks.SelectMany(b => b.Statements.Select((s, i) => (Statement: s, Block: b, Index: i))).ToArray();
        if (!positions.Any(p => ExprMap.Operands(p.Statement).SelectMany(ExprMap.Walk)
            .Any(e => e is Binary { Op: BinOp.Add, Left: FrameAddress, Right: not Const }))) return 0;
        var definitions = positions.Where(p => p.Statement is Define or Phi).ToDictionary(p => p.Statement is Define d ? d.Target : ((Phi)p.Statement).Target);
        var budget = 16384;
        bool FrameValue(Expr e, int depth = 0)
        {
            if (--budget < 0 || depth > 64) return true;
            if (e is Load) return false;
            if (e is FrameAddress) return true;
            if (e is Use u && definitions.TryGetValue(u.Variable, out var p))
                return p.Statement is Define d ? FrameValue(d.Value, depth + 1)
                    : ((Phi)p.Statement).Sources.Any(v => FrameValue(new Use(v, u.Width), depth + 1));
            return ExprMap.Children(e).Any(c => FrameValue(c, depth + 1));
        }
        // 地址被传出或存入其他位置后，未知调用可能改写本帧；本规则不推断这类别名。
        if (positions.Any(p => p.Statement is Store s && FrameValue(s.Value)
            || p.Statement is Call c && ExprMap.Operands(c).Any(e => FrameValue(e)))) return 0;
        var active = new HashSet<(Block, int, long, int)>();
        var values = new Dictionary<Variable, Const?>();
        Const? Same(IEnumerable<Const?> source)
        {
            var all = source.ToArray();
            return all.Length > 0 && all[0] is { } first && all.All(c => c == first) ? first : null;
        }
        Const? Value(Expr e, Block block, int index, int depth)
        {
            if (--budget < 0 || depth > 128 || e.Width > 64) return null;
            switch (e)
            {
                case Const constant: return constant;
                case Use use when definitions.TryGetValue(use.Variable, out var p):
                    if (!values.TryGetValue(use.Variable, out var known))
                    {
                        values[use.Variable] = null;
                        known = p.Statement is Define d ? Value(d.Value, p.Block, p.Index, depth + 1)
                            : Same(((Phi)p.Statement).Sources.Select(v => Value(new Use(v, use.Variable.Width), p.Block, p.Index, depth + 1)));
                        values[use.Variable] = known;
                    }
                    return known is null ? null : Fold.Convert(use.Width < known.Width ? ConvKind.Truncate : ConvKind.ZeroExtend, known, use.Width) as Const;
                case Load { Address: FrameAddress { Offset: < 0 } frame } load:
                    return Read(block, index, frame.Offset, load.Width, depth + 1);
                case Binary binary when Value(binary.Left, block, index, depth + 1) is { } left
                    && Value(binary.Right, block, index, depth + 1) is { } right:
                    return Fold.Binary(binary.Op, left, right, binary.Width) as Const;
                case Ir.Convert conversion when Value(conversion.Operand, block, index, depth + 1) is { } operand:
                    return Fold.Convert(conversion.Kind, operand, conversion.Width) as Const;
                default: return null;
            }
        }
        long? Address(Expr expression, Block block, int index, int depth) => expression switch
        {
            FrameAddress frame => frame.Offset,
            Binary { Op: BinOp.Add, Left: FrameAddress frame } add when Value(add.Right, block, index, depth + 1) is { } offset
                => unchecked(frame.Offset + offset.Signed),
            _ => null,
        };
        Const? Read(Block block, int index, long offset, int width, int depth)
        {
            var key = (block, index, offset, width);
            if (--budget < 0 || depth > 128 || !active.Add(key)) return null;
            Const? result = null;
            var found = false;
            for (var i = index - 1; i >= 0; i--)
            {
                if (block.Statements[i] is not Store store) continue;
                var at = Address(store.Target, block, i, depth + 1);
                if (at is null)
                {
                    if (FrameValue(store.Target)) { found = true; break; }
                    continue;
                }
                if (at >= offset + width / 8 || at + store.Value.Width / 8 <= offset) continue;
                found = true;
                if (at == offset && store.Value.Width == width) result = Value(store.Value, block, i, depth + 1);
                break;
            }
            if (!found) result = Same(block.Predecessors.Select(p =>
                p.NormalSuccessors.Contains(block) || p.Statements.LastOrDefault() is Call
                    ? Read(p, p.Statements.Count, offset, width, depth + 1) : null));
            active.Remove(key);
            return result;
        }
        var changed = 0;
        foreach (var p in positions)
            p.Block.Statements[p.Index] = ExprMap.MapOperands(p.Statement, e => ExprMap.Map(e, part =>
            {
                if (part is not Binary { Op: BinOp.Add, Left: FrameAddress, Right: not Const }
                    || Address(part, p.Block, p.Index, 0) is not { } offset) return null;
                changed++;
                return new FrameAddress(offset);
            }));
        return changed;
    }
}
