using Cpp2CS.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Ssa;

/// <summary>
/// SSA 上的传播与清理：复制/常量/栈地址传播，无 Load 的标志位定义代入条件，平凡 φ 消除，
/// 表达式化简，以及条件边上的 φ 常量来源，然后删除无使用的纯定义。
/// SSA 下变量取值处处相同；条件边的常量仅替换对应的 φ 输入。
/// 带 Load 的表达式不移动（中间可能有写内存），留给后续按区间判定的表达式合并。
/// </summary>
public static class Propagate
{
    public static void Run(MachineFunction function, Dominators dominators)
    {
        while (true)
        {
            var changed = Substitute(function, dominators);
            changed |= EdgeConstants.Run(function) > 0;
            if (!changed) break;
            RemoveDead(function);
        }
        RemoveDead(function);
    }

    /// <summary>可无条件复制到使用处的定义值：叶子、叶子的扩展/截断、叶子加常量、无 Load 的标志位。</summary>
    private static bool Movable(Expr value) => value switch
    {
        Const or Use or FrameAddress or Symbol => true,
        Ir.Convert { Operand: Const or Use or FrameAddress } => true,
        Binary { Op: BinOp.Add or BinOp.Sub, Left: Use or FrameAddress, Right: Const } => true,
        Flags or ConditionalFlags => !ExprMap.Walk(value).Any(e => e is Load or Intrinsic),
        _ => false,
    };

    private static bool Substitute(MachineFunction function, Dominators dominators)
    {
        var replace = new Dictionary<Variable, Expr>();
        var renamed = new Dictionary<Variable, Variable>();
        var definedIn = new Dictionary<Variable, int>();
        foreach (var block in function.Blocks)
            foreach (var stmt in block.Statements)
                foreach (var target in Targets(stmt))
                    definedIn[target] = block.Index;
        // 来源 v 在 φ 所在块入口可用：入口值，或定义块严格支配该块
        bool Reaches(Variable v, int block) => v.Version == 0 || definedIn.TryGetValue(v, out var at) && at != block && dominators.Dominates(at, block);

        foreach (var block in function.Blocks)
            foreach (var stmt in block.Statements)
            {
                if (stmt is Define define && Movable(define.Value))
                {
                    replace[define.Target] = define.Value;
                    if (define.Value is Use use && use.Width == define.Target.Width && use.Variable.Width == use.Width)
                        renamed[define.Target] = use.Variable;
                }
                else if (stmt is Phi phi)
                {
                    // 平凡 φ：除自身与未定义值外只有一个来源。未定义值可取任意值，所以并入唯一来源在语义上成立，
                    // 但带未定义来源时只有该来源支配 φ 所在块才保持 SSA 形式
                    var sources = phi.Sources.Where(v => v != phi.Target).Distinct().ToList();
                    var defined = sources.Where(v => v.Version >= 0).ToList();
                    if (defined.Count == 0)
                    {
                        if (sources.Count > 0) replace[phi.Target] = new Unknown($"{phi.Target.Storage} 被调用破坏", phi.Target.Width);
                    }
                    else if (defined.Count == 1 && (sources.Count == 1 || Reaches(defined[0], block.Index)))
                    {
                        replace[phi.Target] = new Use(defined[0], phi.Target.Width);
                        renamed[phi.Target] = defined[0];
                    }
                }
            }
        if (replace.Count == 0) return false;

        Variable Chase(Variable v)
        {
            var seen = new HashSet<Variable>();
            while (renamed.TryGetValue(v, out var next) && seen.Add(v)) v = next;
            return v;
        }

        var resolved = new Dictionary<Variable, Expr>();
        var resolving = new HashSet<Variable>();
        Expr Value(Variable variable)
        {
            if (resolved.TryGetValue(variable, out var cached)) return cached;
            // φ 环上的复制：保留变量本身
            if (!resolving.Add(variable)) return new Use(variable, variable.Width);
            var value = Resolve(replace[variable]);
            resolving.Remove(variable);
            return resolved[variable] = value;
        }
        Expr Resolve(Expr expr) => Fold.Simplify(ExprMap.Map(expr, e =>
        {
            if (e is not Use use || !replace.ContainsKey(use.Variable)) return null;
            var value = Value(use.Variable);
            return use.Width == value.Width ? value : Fold.Convert(ConvKind.Truncate, value, use.Width);
        }));
        bool Mentions(Expr expr) => ExprMap.Walk(expr).Any(e => e is Use u && replace.ContainsKey(u.Variable));

        var changed = false;
        foreach (var block in function.Blocks)
        {
            var statements = block.Statements;
            for (var i = 0; i < statements.Count; i++)
            {
                var stmt = statements[i];
                Stmt rewritten;
                if (stmt is Phi phi)
                {
                    var sources = phi.Sources.Select(Chase).ToArray();
                    rewritten = sources.AsSpan().SequenceEqual(phi.Sources) ? phi : phi with { Sources = sources };
                }
                else if (stmt is Define define && replace.ContainsKey(define.Target)) continue;
                else rewritten = ExprMap.MapOperands(stmt, e => Mentions(e) ? Resolve(e) : e);
                if (ReferenceEquals(rewritten, stmt)) continue;
                statements[i] = rewritten;
                changed = true;
            }
        }
        return changed;
    }

    private static IEnumerable<Variable> Targets(Stmt stmt) => stmt switch
    {
        Define d => [d.Target],
        Phi p => [p.Target],
        Call c => c.Defines.Where(v => v is not null),
        _ => [],
    };

    /// <summary>删除没有使用的纯定义与 φ（迭代到不动点）。调用、写内存、控制流语句不删。</summary>
    public static void RemoveDead(MachineFunction function)
    {
        var uses = new Dictionary<Variable, int>();
        var definitions = new Dictionary<Variable, Stmt>();
        void Count(Stmt stmt, int delta)
        {
            if (stmt is Phi phi)
            {
                foreach (var source in phi.Sources)
                    if (source != phi.Target) uses[source] = uses.GetValueOrDefault(source) + delta;
                return;
            }
            foreach (var e in ExprMap.Operands(stmt).SelectMany(ExprMap.Walk))
                if (e is Use use) uses[use.Variable] = uses.GetValueOrDefault(use.Variable) + delta;
        }
        foreach (var block in function.Blocks)
            foreach (var stmt in block.Statements)
            {
                Count(stmt, 1);
                if (stmt is Define d) definitions[d.Target] = stmt;
                else if (stmt is Phi p) definitions[p.Target] = stmt;
            }

        var dead = new HashSet<Stmt>(ReferenceEqualityComparer.Instance);
        var work = new Stack<Variable>(definitions.Keys.Where(v => uses.GetValueOrDefault(v) == 0));
        while (work.Count > 0)
        {
            var variable = work.Pop();
            var stmt = definitions[variable];
            if (uses.GetValueOrDefault(variable) != 0 || !dead.Add(stmt)) continue;
            Count(stmt, -1);
            IEnumerable<Variable> operands = stmt is Phi phi ? phi.Sources : ExprMap.Operands(stmt).SelectMany(ExprMap.Walk).OfType<Use>().Select(u => u.Variable);
            foreach (var operand in operands)
                if (uses.GetValueOrDefault(operand) == 0 && definitions.ContainsKey(operand)) work.Push(operand);
        }
        if (dead.Count == 0) return;
        foreach (var block in function.Blocks)
        {
            foreach (var stmt in block.Statements)
                if (stmt is Define d && dead.Contains(stmt)) function.Dead.Add((block, d));
            block.Statements.RemoveAll(dead.Contains);
        }
    }
}
