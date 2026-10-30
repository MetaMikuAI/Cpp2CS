using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>合流后的首个地址读取分发到必经前驱，保留读取顺序和异常区域。</summary>
internal static class AddressPhiLoads
{
    public static bool Run(MachineFunction function, Func<Variable> fresh)
    {
        if (GuardedReads(function, fresh)) return true;
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
            Compare comparison => Pure(comparison.Left) && Pure(comparison.Right),
            Select selection => Pure(selection.Condition) && Pure(selection.True) && Pure(selection.False),
            _ => false,
        };
        var changed = false;
        foreach (var block in function.Blocks)
        {
            if (block.IsLandingPad || block.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Define read
                || block.Predecessors.Count < 2 || block.Predecessors.Any(p => p == block || p.Handler != block.Handler
                    || p.NormalSuccessors.Count() != 1 || !p.NormalSuccessors.Contains(block))) continue;
            var value = read.Value;
            while (value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion)
                value = conversion.Operand;
            if (value is not Load load || load.Address.Width != 64 || !Pure(load.Address)) continue;
            var merged = block.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            var address = Expand(load.Address);
            var inputs = ExprMap.Walk(address).OfType<Use>().Where(u => merged.ContainsKey(u.Variable)).ToArray();
            if (inputs.Length == 0 || inputs.Any(u => merged[u.Variable].Sources.Length != block.Predecessors.Count)) continue;
            // 基址和索引可分别合流；同一前驱的所有来源一起代入，不能交叉组合。
            var addresses = Enumerable.Range(0, block.Predecessors.Count).Select(i => Fold.Simplify(Expand(ExprMap.Map(address,
                e => e is Use use && merged.TryGetValue(use.Variable, out var phi) ? new Use(phi.Sources[i], use.Width) : null)))).ToArray();
            if (addresses.Any(e => !Pure(e) || ExprMap.Walk(e).OfType<Use>().Any(u => merged.ContainsKey(u.Variable)))) continue;
            // 分别合流的扩展限于变址常量表；普通字段、数组保留原读取形态，供后续访问器认回。
            var direct = load.Address is Use pointer && merged.ContainsKey(pointer.Variable);
            if (!direct && addresses.Any(e => e is not Binary { Op: BinOp.Add, Right: Const, Left: Binary { Op: BinOp.Shl, Right: Const scale } }
                || scale.Value > 3 || (1UL << (int)scale.Value) != (ulong)load.Width / 8)) continue;
            var sources = new Variable[addresses.Length];
            for (var i = 0; i < sources.Length; i++)
            {
                var parent = block.Predecessors[i];
                sources[i] = fresh();
                var last = parent.Statements.LastOrDefault();
                parent.Statements.Insert(parent.Statements.Count - (last is Jump ? 1 : 0),
                    new Define(read.Address, sources[i], ExprMap.Map(read.Value, e => ReferenceEquals(e, load) ? load with { Address = addresses[i] } : null)));
            }
            block.Statements.Remove(read);
            block.Statements.Insert(block.Statements.TakeWhile(s => s is Phi).Count(), new Phi(read.Address, read.Target, sources));
            changed = true;
        }
        return changed;
    }

    /// <summary>地址选择之后的判空、边界检查与读取一起移入原分支，不让读取越过检查。</summary>
    private static bool GuardedReads(MachineFunction function, Func<Variable> fresh)
    {
        if (function.Range.ExceptionRegions.Length != 0) return false;
        static Expr Unwrap(Expr value)
        {
            while (value is Ir.Convert { Kind: ConvKind.ZeroExtend or ConvKind.SignExtend or ConvKind.Truncate } conversion) value = conversion.Operand;
            return value;
        }
        foreach (var join in function.Blocks)
        {
            var phis = join.Statements.OfType<Phi>().ToDictionary(p => p.Target);
            if (join.IsLandingPad || join.Handler is not null || join.Predecessors.Count < 2 || phis.Count == 0
                || phis.Values.Any(p => p.Sources.Length != join.Predecessors.Count)
                || join.Predecessors.Any(p => p == join || p.Handler is not null || p.NormalSuccessors.ToArray() is not [var next] || next != join)
                || join.Statements.FirstOrDefault(s => s is not (Phi or Nop)) is not Call { Op.Kind: OpKind.NullCheck }) continue;
            var prefix = new List<(Block Block, Stmt Statement)>();
            var current = join;
            var visited = new HashSet<Block>();
            var reading = false;
            var done = false;
            while (!done && visited.Count < 8 && visited.Add(current))
            {
                foreach (var statement in current.Statements.Where(s => s is not (Phi or Nop or Jump)))
                {
                    if (statement is Define read && Unwrap(read.Value) is Load { Address: Use pointer }
                        && phis.ContainsKey(pointer.Variable)) reading = true;
                    else if (reading || statement is not Call { Op.Kind: OpKind.NullCheck or OpKind.BoundsCheck, Defines.Length: 0 }
                        && (statement is not Define length || Unwrap(length.Value) is not Load
                        { Width: 32, Address: Binary { Op: BinOp.Add, Right: Const { Value: Facts.RuntimeLayout.ArrayMaxLength } } }))
                    { done = true; break; }
                    prefix.Add((current, statement));
                    if (prefix.Count >= 16) { done = true; break; }
                }
                if (reading || done || current.NormalSuccessors.ToArray() is not [var next] || next.IsLandingPad || next.Handler is not null
                    || next.Predecessors.Count != 1 || next.Statements.Any(s => s is Phi)) break;
                current = next;
            }
            if (!reading) continue;
            var definitions = prefix.Select(p => p.Statement).OfType<Define>().ToArray();
            var results = definitions.ToDictionary(d => d.Target, _ => new List<Variable>());
            for (var side = 0; side < join.Predecessors.Count; side++)
            {
                var mapped = phis.ToDictionary(p => p.Key, p => p.Value.Sources[side]);
                Expr OnEdge(Expr expression) => ExprMap.Map(expression, e => e is Use use && mapped.TryGetValue(use.Variable, out var source)
                    ? new Use(source, use.Width) : null);
                var parent = join.Predecessors[side];
                var position = parent.Statements.Count - (parent.Statements.LastOrDefault() is Jump ? 1 : 0);
                foreach (var (_, statement) in prefix)
                {
                    // 操作数未变时改写器会返回原对象；每条入边仍需独立的语句身份。
                    var copy = ExprMap.MapOperands(statement, OnEdge) with { };
                    if (copy is Define define)
                    {
                        var target = fresh();
                        mapped[define.Target] = target;
                        results[define.Target].Add(target);
                        copy = define with { Target = target };
                    }
                    parent.Statements.Insert(position++, copy);
                }
            }
            foreach (var (block, statement) in prefix) block.Statements.Remove(statement);
            foreach (var definition in definitions) join.Statements.Insert(0, new Phi(definition.Address, definition.Target, results[definition.Target].ToArray()));
            return true;
        }
        return false;
    }
}
