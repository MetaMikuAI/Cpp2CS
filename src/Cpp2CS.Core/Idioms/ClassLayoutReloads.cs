using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Idioms;

/// <summary>类布局守卫两侧读取同一大小字段时，统一保留初始化后的读取。</summary>
internal static class ClassLayoutReloads
{
    internal static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr e, Variable? result = null, Expr? subject = null, int depth = 0) => depth > 24 ? e : Fold.Simplify(ExprMap.Map(e, part =>
            part is Use u ? u.Variable == result ? subject : definitions.TryGetValue(u.Variable, out var value) ? Expand(value, result, subject, depth + 1) : null : null));
        foreach (var head in function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.ToArray() is not [var taken, var fallthrough]) continue;
            var condition = Expand(branch.Condition);
            if (ExprMap.Walk(condition).OfType<Load>().Distinct().ToArray() is not [var flag]
                || flag.Address is not Binary { Op: BinOp.Add, Left: Symbol { Kind: SymbolKind.Class, Value: TypeRef type } klass,
                    Right: Const { Value: RuntimeLayout.ClassBitflags1 } }
                || !ClassInitializationFlags.IsBitTest(condition, flag)) continue;
            var clear = Fold.Simplify(ExprMap.Map(condition, e => e == flag ? Expr.C(0, flag.Width) : null));
            var set = Fold.Simplify(ExprMap.Map(condition, e => e == flag ? Expr.C(1, flag.Width) : null));
            if (clear is not Const zero || set is not Const one || zero.Value == one.Value) continue;
            var initialize = zero.Value != 0 ? taken : fallthrough;
            var skip = zero.Value != 0 ? fallthrough : taken;
            if (initialize.Predecessors.ToArray() is not [var parent] || parent != head || initialize.Handler != head.Handler
                || initialize.NormalSuccessors.ToArray() is not [var merge] || initialize.IsLandingPad
                || skip == merge || skip.Predecessors.ToArray() is not [var skipParent] || skipParent != head
                || skip.NormalSuccessors.ToArray() is not [var skipMerge] || skipMerge != merge || skip.Handler != head.Handler || skip.IsLandingPad
                || initialize.Statements.OfType<Call>().ToArray() is not [var call]
                || call is not { Op.Kind: OpKind.InitClass, Arguments: [var argument], Defines: [var result] }
                || !Equals(call.Op.Operand, type) || Expand(argument) != klass) continue;
            var size = new Load(new Binary(BinOp.Add, klass, Expr.C(RuntimeLayout.ClassStackSlotSize, 64), 64), 32);
            bool Size(Expr value)
            {
                value = Expand(value, result, klass);
                return value == size || value is Ir.Convert { Kind: ConvKind.ZeroExtend, Width: 64, Operand: var operand } && operand == size;
            }
            var after = initialize.Statements.Skip(initialize.Statements.IndexOf(call) + 1).ToArray();
            if (initialize.Statements.Take(initialize.Statements.IndexOf(call)).Any(s => s is not Nop)
                || !after.OfType<Define>().Any() || after.Any(s => s is not (Nop or Jump) && !(s is Define d && Size(d.Value)))
                || skip.Statements.Any(s => s is not (Nop or Jump) && !(s is Define d && Size(d.Value)))) continue;
            var initializedEdge = merge.Predecessors.IndexOf(initialize);
            var skippedEdge = merge.Predecessors.IndexOf(skip);
            if (merge.Statements.OfType<Phi>().Any(p => p.Sources.Length != merge.Predecessors.Count
                || Expand(new Use(p.Sources[initializedEdge], p.Target.Width), result, klass)
                    != Expand(new Use(p.Sources[skippedEdge], p.Target.Width)))) continue;
            head.Statements[^1] = new Jump(branch.Address, initialize.Start);
            MachineFunction.RemoveEdge(head, skip);
            return true;
        }
        return false;
    }
}
