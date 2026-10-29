using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>接口查找的快慢路径均产生同一接收者的 VirtualInvokeData；只证明尾调用，不删除原始输入读取。</summary>
internal static class InterfaceTailProof
{
    public static HashSet<Call> Find(MachineFunction function, Func<Call, bool> isLookup)
    {
        var statements = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var tails = statements.OfType<Call>().Where(c => c is { Kind: CallKind.TailIndirect, Op: null }).ToArray();
        if (tails.Length == 0) return [];
        var definitions = statements.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        var phis = statements.OfType<Phi>().ToDictionary(p => p.Target);
        var lookups = statements.OfType<Call>().Where(c => c.Arguments.Length == 3 && c.Defines.Length == 1
            && c.Results is [var result] && result == Storage.Gpr(0) && isLookup(c)).ToDictionary(c => c.Defines[0]);
        var proven = new HashSet<Call>(ReferenceEqualityComparer.Instance);
        Expr Expand(Expr value, int depth = 32) => depth == 0 ? value : Fold.Simplify(ExprMap.Map(value,
            e => e is Use use && definitions.TryGetValue(use.Variable, out var source) && use.Width <= source.Width
                ? Expand(Fold.Convert(ConvKind.Truncate, source, use.Width), depth - 1) : null));
        foreach (var tail in tails)
        {
            if (tail.Arguments.Length == 0 || Expand(tail.Target) is not Load { Width: 64, Address: Use data }
                || !phis.TryGetValue(data.Variable, out var phi) || phi.Sources.Length != 2) continue;
            var receiver = Expand(tail.Arguments[0]);
            var info = new Load(Fold.Simplify(new Binary(BinOp.Add, data, Expr.C(8, 64), 64)), 64);
            if (!tail.Arguments.Select(a => Expand(a)).Contains(info)) continue;
            for (var side = 0; side < 2; side++)
            {
                if (Expand(new Use(phi.Sources[side], 64)) is not Use slow || !lookups.TryGetValue(slow.Variable, out var lookup)
                    || Expand(lookup.Arguments[0]) != receiver || Expand(lookup.Arguments[2]) is not Const { Value: <= ushort.MaxValue } slot) continue;
                var fast = Expand(new Use(phi.Sources[1 - side], 64));
                var terms = Terms(fast).ToArray();
                var constant = terms.OfType<Const>().Aggregate(0UL, (sum, c) => sum + c.Value);
                var klass = new Load(receiver, 64);
                var scaled = terms.Where(t => t is not Const && t != klass).ToArray();
                if (terms.Count(t => t == klass) != 1
                    || scaled is not [Binary { Op: BinOp.Shl, Width: 64, Right: Const { Value: 4 }, Left: Ir.Convert { Kind: ConvKind.SignExtend, Operand: var index, Width: 64 } }]) continue;
                var offset = index;
                if (constant == RuntimeLayout.ClassVtable && slot.Value != 0)
                {
                    if (index is not Binary { Op: BinOp.Add, Width: 32, Right: Const increment } add || increment.Value != slot.Value) continue;
                    offset = add.Left;
                }
                else if (constant != (ulong)RuntimeLayout.VtableMethodPointer((int)slot.Value)) continue;
                if (offset is not Load { Width: 32 }) continue;
                proven.Add(tail);
                break;
            }
        }
        return proven;
    }

    private static IEnumerable<Expr> Terms(Expr value) => value is Binary { Op: BinOp.Add, Width: 64 } add
        ? Terms(add.Left).Concat(Terms(add.Right)) : [value];
}
