using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>合流后的首个地址读取分发到必经前驱，保留读取顺序和异常区域。</summary>
internal static class AddressPhiLoads
{
    public static bool Run(MachineFunction function, Func<Variable> fresh)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr expression, int depth = 0)
        {
            if (depth >= 16) return expression;
            if (expression is Use use)
                return definitions.TryGetValue(use.Variable, out var value) && Pure(value)
                    ? Fold.Convert(ConvKind.Truncate, Expand(value, depth + 1), use.Width) : expression;
            return ExprMap.Map(expression, part => part is Use ? Expand(part, depth + 1) : null);
        }
        static bool Pure(Expr value) => value switch
        {
            Const or Use or Symbol => true,
            Binary { Op: BinOp.Add or BinOp.Sub or BinOp.Mul or BinOp.Shl or BinOp.LShr or BinOp.AShr or BinOp.And or BinOp.Or or BinOp.Xor } binary
                => Pure(binary.Left) && Pure(binary.Right),
            Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion => Pure(conversion.Operand),
            _ => false,
        };
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.IsLandingPad || block.Statements.FirstOrDefault(s => s is not (Phi or Nop))
                is not Define { Value: Load { Address: Use pointer } load } read
                || block.Statements.OfType<Phi>().FirstOrDefault(p => p.Target == pointer.Variable) is not { } phi
                || pointer.Width != 64 || phi.Sources.Length != block.Predecessors.Count
                || block.Predecessors.Count < 2 || block.Predecessors.Any(p => p == block || p.Handler != block.Handler
                    || p.NormalSuccessors.Count() != 1 || !p.NormalSuccessors.Contains(block))) continue;
            var merged = block.Statements.OfType<Phi>().Select(p => p.Target).ToHashSet();
            var addresses = phi.Sources.Select(v => Expand(new Use(v, 64))).ToArray();
            if (addresses.Any(e => !Pure(e) || ExprMap.Walk(e).OfType<Use>().Any(u => merged.Contains(u.Variable)))) continue;
            var sources = new Variable[addresses.Length];
            for (var i = 0; i < sources.Length; i++)
            {
                var parent = block.Predecessors[i];
                sources[i] = fresh();
                var last = parent.Statements.LastOrDefault();
                parent.Statements.Insert(parent.Statements.Count - (last is Jump ? 1 : 0),
                    new Define(read.Address, sources[i], load with { Address = addresses[i] }));
            }
            block.Statements.Remove(read);
            block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Phi(read.Address, read.Target, sources));
            changed = true;
        }
        return changed;
    }
}
