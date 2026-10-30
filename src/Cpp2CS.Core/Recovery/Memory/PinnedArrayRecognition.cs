using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Recovery;

/// <summary>空引用或空数组取零，否则取首元素地址；只合并已有分支证明的地址选择。</summary>
internal static class PinnedArrayRecognition
{
    private enum Guard { NullOrEmpty, NonNull, NonEmpty }

    internal static int Run(MachineFunction function, Func<Expr, ArrayRef?> arrayType)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr value, int depth = 0)
        {
            if (depth > 24 || arrayType(value) is not null) return value;
            return value is Use use && definitions.TryGetValue(use.Variable, out var source)
                ? ScalarVectorNarrowing.Low(Expand(source, depth + 1), use.Width) : value;
        }
        Expr? Root(Expr value)
        {
            value = Expand(value);
            return value is Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ArrayData } } address && arrayType(address.Left) is not null
                ? address.Left : value is Select choice ? Root(choice.True) ?? Root(choice.False) : null;
        }
        bool Length(Expr value, Expr root)
        {
            value = Expand(value);
            if (value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.Truncate } conversion) value = Expand(conversion.Operand);
            return value is Load { Width: 32 or 64, Address: Binary { Op: BinOp.Add, Right: Const { Value: RuntimeLayout.ArrayMaxLength } } address }
                && address.Left == root;
        }
        bool Test(Expr condition, bool taken, Expr root, Guard guard)
        {
            if (condition is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } comparison) return false;
            var zero = taken == (comparison.Cond == Cond.Eq);
            return guard switch
            {
                Guard.NullOrEmpty => zero && (Expand(comparison.Left) == root || Length(comparison.Left, root)),
                Guard.NonNull => !zero && Expand(comparison.Left) == root,
                Guard.NonEmpty => !zero && Length(comparison.Left, root),
                _ => false,
            };
        }
        bool Edge(Block from, Block to, Expr root, Guard guard, HashSet<Block> seen)
        {
            if (!from.NormalSuccessors.Contains(to)) return false;
            if (from.Statements.LastOrDefault() is Branch branch && branch.Target != branch.Fallthrough
                && Test(branch.Condition, branch.Target == to.Start, root, guard)) return true;
            if (seen.Count >= 32 || !seen.Add(from) || from.Predecessors.Count == 0) return false;
            var proven = from.Predecessors.All(p => Edge(p, from, root, guard, seen));
            seen.Remove(from);
            return proven;
        }
        bool Source(Expr value, Block from, Block to, Expr root)
        {
            value = Expand(value);
            if (value is Const { Value: 0, Width: 64 }) return Edge(from, to, root, Guard.NullOrEmpty, []);
            if (value is Binary && Root(value) == root)
                return Edge(from, to, root, Guard.NonNull, []) && Edge(from, to, root, Guard.NonEmpty, []);
            if (value is not Select choice || !Edge(from, to, root, Guard.NonNull, [])) return false;
            var zeroTrue = Expand(choice.True) is Const { Value: 0 };
            var data = zeroTrue ? choice.False : choice.True;
            var zero = zeroTrue ? choice.True : choice.False;
            return Expand(zero) is Const { Value: 0 } && Expand(data) is Binary && Root(data) == root
                && Test(choice.Condition, !zeroTrue, root, Guard.NonEmpty);
        }
        var changed = 0;
        foreach (var block in function.Blocks)
            foreach (var phi in block.Statements.OfType<Phi>().ToArray())
            {
                if (phi.Target.Width != 64 || phi.Sources.Length != 2 || block.Predecessors.Count != 2) continue;
                var roots = phi.Sources.Select(v => Root(new Use(v, 64))).OfType<Expr>().Distinct().ToArray();
                if (roots is not [var root] || !phi.Sources.Select((v, i) => Source(new Use(v, 64), block.Predecessors[i], block, root)).All(v => v)) continue;
                block.Statements[block.Statements.IndexOf(phi)] = new Define(phi.Address, phi.Target, new Intrinsic("pinned_array_start", [root], 64));
                changed++;
            }
        return changed;
    }
}
