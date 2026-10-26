using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Ssa;

namespace Cpp2CS.Recovery;

/// <summary>同一循环的元素指针与整数下标按对应步长递增时，恢复数组根和下标关系。</summary>
internal static class ArrayCursorRecognition
{
    internal sealed record Cursor(Variable Pointer, Expr Address, IReadOnlySet<Variable> AddressCopies);

    public static IEnumerable<Cursor> Read(MachineFunction function, Func<Expr, int?> elementSize)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements.OfType<Define>()).ToDictionary(d => d.Target, d => d.Value);
        var locations = function.Blocks.SelectMany(b => b.Statements.SelectMany(s => s switch
        { Define d => new[] { d.Target }, Phi p => [p.Target], Call c => c.Defines.Where(v => v is not null), _ => [] }).Select(v => (Variable: v, Block: b)))
            .ToDictionary(p => p.Variable, p => p.Block);
        var dominators = Dominators.Compute(function);
        Expr Expand(Expr expression, HashSet<Variable>? seen = null)
        {
            seen ??= [];
            if (elementSize(expression) is not null) return expression;
            if (expression is Use use && seen.Add(use.Variable) && definitions.TryGetValue(use.Variable, out var value)
                && value is Use or Const or Binary { Op: BinOp.Add or BinOp.Sub }) return Expand(value, seen);
            return expression is Binary { Op: BinOp.Add or BinOp.Sub } binary
                ? Fold.Simplify(binary with { Left = Expand(binary.Left, seen), Right = Expand(binary.Right, seen) }) : expression;
        }
        long? Step(Variable source, Variable target)
        {
            var value = Expand(new Use(source, 64));
            if (value is Use same && same.Variable == target) return 0;
            return value is Binary { Op: BinOp.Add, Left: Use previous, Right: Const amount } && previous.Variable == target ? amount.Signed : null;
        }
        (Expr Root, long Offset, int Size)? Seed(Variable source, Block loop)
        {
            var value = Expand(new Use(source, 64));
            long offset = 0;
            while (value is Binary { Op: BinOp.Add, Right: Const constant } addition) { offset += constant.Signed; value = addition.Left; }
            if (value is not Use root || elementSize(root) is not { } size || size <= 0 || offset < Facts.RuntimeLayout.ArrayData
                || root.Variable.Version != 0 && (!locations.TryGetValue(root.Variable, out var block) || block == loop || !dominators.Dominates(block.Index, loop.Index))) return null;
            return (root, offset, size);
        }
        foreach (var block in function.Blocks)
        foreach (var pointer in block.Statements.OfType<Phi>().Where(p => p.Target.Width == 64))
        foreach (var counter in block.Statements.OfType<Phi>().Where(p => p != pointer && p.Target.Width == 64 && p.Sources.Length == pointer.Sources.Length))
        {
            Expr? root = null;
            long origin = 0;
            var size = 0;
            var valid = true;
            var hasStep = false;
            for (var i = 0; i < pointer.Sources.Length; i++)
            {
                if (Step(pointer.Sources[i], pointer.Target) is { } pointerStep && Step(counter.Sources[i], counter.Target) is { } counterStep)
                {
                    var ratio = counterStep == 0 ? 0 : (Int128)pointerStep / counterStep;
                    if (counterStep == 0 ? pointerStep != 0 : pointerStep == 0 || (Int128)pointerStep % counterStep != 0
                        || ratio <= 0 || ratio > int.MaxValue) { valid = false; break; }
                    if (counterStep != 0)
                    {
                        var scale = (int)(pointerStep / counterStep);
                        if (size != 0 && size != scale) { valid = false; break; }
                        size = scale; hasStep = true;
                    }
                    continue;
                }
                if (Seed(pointer.Sources[i], block) is not { } seed || Expand(new Use(counter.Sources[i], 64)) is not Const initial
                    || size != 0 && size != seed.Size) { valid = false; break; }
                var bias = (Int128)seed.Offset - (Int128)initial.Signed * seed.Size;
                if (bias < long.MinValue || bias > long.MaxValue || root is not null && (root != seed.Root || origin != (long)bias)) { valid = false; break; }
                root = seed.Root; origin = (long)bias; size = seed.Size;
            }
            if (!valid || root is null || !hasStep) continue;
            var copies = new HashSet<Variable>();
            void Collect(Variable variable)
            {
                if (variable == pointer.Target || variable == counter.Target || elementSize(new Use(variable, 64)) is not null
                    || !definitions.TryGetValue(variable, out var value) || !copies.Add(variable)) return;
                foreach (var use in ExprMap.Walk(value).OfType<Use>()) Collect(use.Variable);
            }
            foreach (var source in pointer.Sources) Collect(source);
            var scaled = new Binary(BinOp.Mul, new Use(counter.Target, 64), Expr.C((ulong)size, 64), 64);
            yield return new(pointer.Target, new Binary(BinOp.Add, new Binary(BinOp.Add, root, Expr.C(unchecked((ulong)origin), 64), 64), scaled, 64), copies);
            break;
        }
    }
}
