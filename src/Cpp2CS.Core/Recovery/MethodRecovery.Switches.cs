using Cpp2CS.Flow;
using Cpp2CS.Ir;
using Cpp2CS.Recovery.Analysis;

namespace Cpp2CS.Recovery;

public sealed partial class MethodRecovery
{
    private sealed partial class Context
    {
        private readonly Dictionary<IndirectJump, Expr> switchIndices = new(ReferenceEqualityComparer.Instance);

        /// <summary>
        /// 跳转表（CFG 已按表项解析出目标，<see cref="IndirectJump.Targets"/>[i] 是下标 i 的目标）：目标地址形如
        /// 表基址 + ext(table[下标 × 项宽]) &lt;&lt; k，例如多个 await 的 MoveNext 按状态分派。地址计算中的定义（读常量表、移位、加基址）
        /// 只服务于这次跳转，标为运行时值不再翻译；下标保留为托管值，跳转翻译成 switch（越界由前驱中的上界检查排除，见 JumpTables）。
        /// </summary>
        [Analysis("跳转表", 45, After = ["运行时引用"])]
        private void JumpTables()
        {
            foreach (var block in blocks)
            {
                if (block.Statements.LastOrDefault() is not IndirectJump { Targets.Length: > 0 } jump) continue;
                var computation = new HashSet<Variable>();
                var expandedIndices = new Dictionary<Variable, Expr>();
                // 表项读取的地址只展开纯运算（不含访存）的定义；下标变量本身（例如读出的状态字段）保留。
                Expr Shallow(Expr e) => ExprMap.Map(e, x => x is Use u && values.TryGetValue(u.Variable, out var v) && !ExprMap.Walk(v).Any(w => w is Load)
                    ? ExpandIndex(u.Variable, Shallow(v)) : null);
                Expr ExpandIndex(Variable variable, Expr value)
                {
                    expandedIndices[variable] = value;
                    return Track(variable, value);
                }
                Expr Target(Expr e) => ExprMap.Map(e, x => x switch
                {
                    Use u when values.TryGetValue(u.Variable, out var v) => Track(u.Variable, Target(v)),
                    Load l => l with { Address = Shallow(l.Address) },
                    _ => null,
                });
                Expr Track(Variable variable, Expr value)
                {
                    computation.Add(variable);
                    return value;
                }
                var target = Target(jump.Target);
                var loads = ExprMap.Walk(target).OfType<Load>().ToArray();
                if (loads is not [var table]) continue;
                var terms = new List<Expr>();
                void Add(Expr e)
                {
                    if (e is Binary { Op: BinOp.Add } b) { Add(b.Left); Add(b.Right); }
                    else terms.Add(e);
                }
                Add(table.Address);
                if (terms.Count(t => t is not Const) != 1 || !terms.Any(t => t is Const)) continue;
                var scaled = terms.Single(t => t is not Const);
                var size = table.Width / 8;
                Expr? index = scaled switch
                {
                    Binary { Op: BinOp.Shl, Right: Const shift } s when (1L << (int)shift.Value) == size => s.Left,
                    Binary { Op: BinOp.Mul, Right: Const factor } m when (long)factor.Value == size => m.Left,
                    _ when size == 1 => scaled,
                    _ => null,
                };
                if (index is null || ExprMap.Walk(index).Any(e => e is Load)) continue;
                var indexVariables = ExprMap.Walk(index).OfType<Use>().Select(u => u.Variable).ToHashSet();
                computation.ExceptWith(indexVariables);
                // 上界检查可能复用展开前的索引。它及索引的纯计算仍是托管值，不属于跳转地址。
                var indexExpressions = ExprMap.Walk(index).ToHashSet();
                computation.ExceptWith(expandedIndices.Where(p => indexExpressions.Contains(p.Value)).Select(p => p.Key));
                // 地址计算的中间值若还有别的使用，就不是只服务于跳转的值。
                var uses = blocks.SelectMany(b => b.Statements).Where(s => s is not Define d || !computation.Contains(d.Target))
                    .Where(s => s != jump).SelectMany(s => s is Phi phi ? phi.Sources.AsEnumerable() : ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable));
                if (uses.Any(computation.Contains)) continue;
                foreach (var variable in computation) runtime.Add(variable);
                switchIndices[jump] = index;
                callBindings.InvalidateTypes();
            }
        }

        [StatementRule(30)]
        private RecoveryResult<bool> LowerSwitch(Block block, Stmt statement, List<ManagedStatement> output)
        {
            if (statement is not IndirectJump jump || !switchIndices.TryGetValue(jump, out var index)) return false;
            var successors = block.NormalSuccessors.Select(b => b.Start).ToList();
            var cases = new List<ManagedEdge>();
            foreach (var target in jump.Targets)
            {
                if (!Edge(block, successors.IndexOf(target), target).TryGet(out var edge, out var failure)) return failure;
                cases.Add(edge);
            }
            if (!Index(index).TryGet(out var value, out var indexFailure)) return indexFailure;
            output.Add(new ManagedSwitch(jump.Address, value, cases));
            return true;
        }
    }
}
