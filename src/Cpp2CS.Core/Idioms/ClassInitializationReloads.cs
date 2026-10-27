using Cpp2CS.Facts;
using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Model;

namespace Cpp2CS.Idioms;

/// <summary>类构造守卫中的字段重读：跳过初始化时已有相同快照，统一保留初始化后的读取。</summary>
internal static class ClassInitializationReloads
{
    internal static bool Run(MachineFunction function)
    {
        var definitions = function.Blocks.SelectMany(b => b.Statements).OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        Expr Expand(Expr value, int depth = 0) => depth >= 32 ? value : ExprMap.Map(value,
            e => e is Use u && definitions.TryGetValue(u.Variable, out var source) ? Expand(source, depth + 1) : null);
        Expr Strip(Expr value)
        {
            value = Expand(value);
            while (value is Ir.Convert c) value = c.Operand;
            return value;
        }
        foreach (var head in function.Blocks)
        {
            if (head.Statements.LastOrDefault() is not Branch branch || head.NormalSuccessors.Count() != 2
                || Expand(branch.Condition) is not Compare { Cond: Cond.Eq or Cond.Ne, Right: Const { Value: 0 } } test
                || Strip(test.Left) is not Load { Width: 32, Address: Binary { Op: BinOp.Add,
                    Left: Symbol { Kind: SymbolKind.Class, Value: DefinitionRef type }, Right: Const { Value: RuntimeLayout.ClassCctorFinishedOrNoCctor } } }) continue;
            var enterAddress = test.Cond == Cond.Eq ? branch.Target : branch.Fallthrough;
            var enter = head.NormalSuccessors.Single(b => b.Start == enterAddress);
            var merge = head.NormalSuccessors.Single(b => b != enter);
            var chain = new List<Block>();
            var previous = head;
            var current = enter;
            while (current != merge && chain.Count < 32 && !chain.Contains(current) && current.Predecessors.Contains(previous)
                && !current.IsLandingPad && current.NormalSuccessors.Count() == 1 && current.Statements.LastOrDefault() is not Branch)
            {
                chain.Add(current);
                previous = current;
                current = current.NormalSuccessors.Single();
            }
            if (current != merge || chain.Count == 0) continue;
            var shared = chain.Any(b => b.Predecessors.Count != 1);
            if (shared)
            {
                // 共用初始化尾部只传递已有值；强制经过该尾部不能改变最终合流值。
                var copies = new Dictionary<Variable, Expr>();
                Expr Value(Variable variable) => copies.GetValueOrDefault(variable) ?? new Use(variable, variable.Width);
                var validPath = true;
                previous = head;
                foreach (var block in chain)
                {
                    if (block.Handler != head.Handler) { validPath = false; break; }
                    var incoming = block.Predecessors.IndexOf(previous);
                    foreach (var statement in block.Statements)
                    {
                        if (statement is Phi phi && phi.Sources.Length == block.Predecessors.Count)
                            copies[phi.Target] = Value(phi.Sources[incoming]);
                        else if (statement is not (Nop or Jump or Call { Op.Kind: OpKind.RunClassConstructor }))
                        { validPath = false; break; }
                    }
                    previous = block;
                }
                var direct = merge.Predecessors.IndexOf(head);
                var initializedPath = merge.Predecessors.IndexOf(chain[^1]);
                if (!validPath || direct < 0 || initializedPath < 0 || merge.Statements.OfType<Phi>().Any(p =>
                    p.Sources.Length != merge.Predecessors.Count || Value(p.Sources[direct]) != Value(p.Sources[initializedPath]))) continue;
            }
            bool PreviousRead(Expr value, bool check)
            {
                value = Expand(value);
                var visited = new HashSet<Block>();
                var block = head;
                while (visited.Add(block))
                {
                    foreach (var statement in block.Statements.AsEnumerable().Reverse())
                    {
                        if (check && statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var subject] } && Expand(subject) == value) return true;
                        if (!check && statement is Define define && Expand(define.Value) == value) return true;
                        if (statement is not (Define or Phi or Nop or Jump or Branch or Call { Op.Kind: OpKind.NullCheck })) return false;
                    }
                    if (block.IsLandingPad || block.Predecessors.Count != 1) return false;
                    block = block.Predecessors[0];
                }
                return false;
            }
            var initialized = false;
            var valid = true;
            foreach (var statement in chain.SelectMany(b => b.Statements))
            {
                if (statement is Nop or Jump || shared && statement is Phi) continue;
                if (!initialized && statement is Call { Op: { Kind: OpKind.RunClassConstructor, Operand: DefinitionRef owner } }
                    && owner.Equals(type)) { initialized = true; continue; }
                if (statement is Define d && ExprMap.Walk(d.Value).All(e => e is Use or Const or Symbol or Binary or Unary or Ir.Convert
                    || initialized && e is Load load && PreviousRead(load, false))) continue;
                if (initialized && statement is Call { Op.Kind: OpKind.NullCheck, Arguments: [var value] } && PreviousRead(value, true)) continue;
                valid = false;
                break;
            }
            if (!valid || !initialized) continue;
            head.Statements[^1] = new Jump(branch.Address, enter.Start);
            MachineFunction.RemoveEdge(head, merge);
            return true;
        }
        return false;
    }
}
