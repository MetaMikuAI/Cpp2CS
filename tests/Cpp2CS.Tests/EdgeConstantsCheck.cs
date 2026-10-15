using Cpp2CS.Flow;
using Cpp2CS.Functions;
using Cpp2CS.Ir;
using Cpp2CS.Managed;
using Cpp2CS.Ssa;

namespace Cpp2CS.Tests;

internal static class EdgeConstantsCheck
{
    public static int Run(string? binary, string? metadata)
    {
        var x = new Variable(Storage.Gpr(0), 0);
        var y = new Variable(Storage.Gpr(1), 0);
        var other = new Variable(Storage.Gpr(0), 1);
        var merged = new Variable(Storage.Gpr(0), 2);
        var samples = new ulong[] { 0, 1, 7, 8, uint.MaxValue, 0x1_0000_0000, 0x8000_0000_0000_0000, ulong.MaxValue };
        Expr Eq(Variable variable, ulong value, int width = 64) => new Compare(Cond.Eq, new Use(variable, width), Expr.C(value, width));
        Expr Ne(Variable variable, ulong value) => new Compare(Cond.Ne, new Use(variable, 64), Expr.C(value, 64));
        MachineFunction Diamond(Expr condition, bool taken, bool differentVersion = false)
        {
            var entry = new Block(0x1000) { Statements = [new Define(0x1000, new Variable(Storage.Temp(0), 1), Expr.C(13, 64))] };
            if (differentVersion) entry.Statements.Add(new Define(0x1000, other, new Binary(BinOp.Add, new Use(x, 64), Expr.C(1, 64), 64)));
            entry.Statements.Add(new Branch(0x1000, condition, taken ? 0x3000UL : 0x2000UL, taken ? 0x2000UL : 0x3000UL));
            var alternate = new Variable(Storage.Gpr(2), 1);
            return Graph(entry,
                new Block(0x2000) { Statements = [new Define(0x2000, alternate, new Binary(BinOp.Add, new Use(x, 64), Expr.C(5, 64), 64)), new Jump(0x2004, 0x3000)] },
                new Block(0x3000) { Statements = [new Phi(0x3000, merged, [differentVersion ? other : x, alternate]), new Return(0x3004) { Value = new Use(merged, 64) }] });
        }
        var checkedInputs = 0;
        void Compare(string name, Func<MachineFunction> make, int replacements)
        {
            var original = make();
            var rewritten = make();
            Require(EdgeConstants.Run(rewritten) == replacements, name + " 的替换数量");
            Require(EdgeConstants.Run(rewritten) == 0, name + " 的重复运行必须稳定");
            Require(SsaCheck.Verify(rewritten, Dominators.Compute(rewritten)).Count == 0, name + " 的 SSA 不变量");
            foreach (var a in samples)
            foreach (var b in samples)
            {
                Require(Execute(original, x, a, y, b) == Execute(rewritten, x, a, y, b), name + " 的改写前后位型");
                checkedInputs++;
            }
        }
        Compare("相等真边", () => Diamond(Eq(x, 0), true), 1);
        Compare("非零常量", () => Diamond(Eq(x, 7), true), 1);
        Compare("不等假边", () => Diamond(Ne(x, 7), false), 1);
        Compare("相等假边", () => Diamond(Eq(x, 7), false), 0);
        Compare("不等真边", () => Diamond(Ne(x, 7), true), 0);
        Compare("交换比较操作数", () => Diamond(new Compare(Cond.Eq, Expr.C(7, 64), new Use(x, 64)), true), 1);
        Compare("逻辑取反", () => Diamond(new Not(Ne(x, 7)), true), 1);
        Compare("合取真边", () => Diamond(new Logical(true, Eq(x, 7), Eq(y, 0)), true), 1);
        Compare("析取假边", () => Diamond(new Logical(false, Ne(x, 7), Ne(y, 0)), false), 1);
        Compare("合取假边", () => Diamond(new Logical(true, Eq(x, 7), Eq(y, 0)), false), 0);
        Compare("析取真边", () => Diamond(new Logical(false, Eq(x, 7), Eq(y, 0)), true), 0);
        Compare("矛盾条件", () => Diamond(new Logical(true, Eq(x, 7), Eq(x, 8)), true), 0);
        Compare("部分位宽", () => Diamond(Eq(x, 0, 32), true), 0);
        Compare("浮点正负零", () => Diamond(new Compare(Cond.FEq, new Use(x, 64), Expr.C(0, 64)), true), 0);
        Compare("不同 SSA 版本", () => Diamond(Eq(x, 7), true, true), 0);
        Compare("重合分支", () => Graph(
            new Block(0x1000) { Statements = [new Define(0x1000, other, Expr.C(9, 64)), new Branch(0x1004, Eq(x, 7), 0x2000, 0x2000)] },
            new Block(0x2000) { Statements = [new Phi(0x2000, merged, [x, other]), new Return(0x2004) { Value = new Use(merged, 64) }] }), 0);

        MachineFunction Loop(bool equal = false) => Graph(
            new Block(0x1000) { Statements = [new Jump(0x1000, 0x2000)] },
            new Block(0x2000) { Statements = [new Phi(0x2000, merged, [x, other]),
                new Define(0x2004, other, new Binary(BinOp.Sub, new Use(merged, 64), Expr.C(1, 64), 64)),
                new Branch(0x2008, equal ? Eq(other, 0) : Ne(other, 0), 0x2000, 0x3000)] },
            new Block(0x3000) { Statements = [new Phi(0x3000, new Variable(Storage.Gpr(3), 1), [other]),
                new Return(0x3004) { Value = new Use(new Variable(Storage.Gpr(3), 1), 64) }] });
        var beforeLoop = Loop(); var afterLoop = Loop();
        Require(EdgeConstants.Run(afterLoop) == 1, "循环退出边的零值");
        Require(SsaCheck.Verify(afterLoop, Dominators.Compute(afterLoop)).Count == 0, "循环改写保留 SSA");
        for (ulong n = 1; n <= 20; n++)
        {
            Require(Execute(beforeLoop, x, n, y, 0) == Execute(afterLoop, x, n, y, 0), "循环边常量不泄漏到回边");
            checkedInputs++;
        }
        Propagate.Run(afterLoop, Dominators.Compute(afterLoop));
        Require(SsaCheck.Verify(afterLoop, Dominators.Compute(afterLoop)).Count == 0, "常量传播后保留 SSA");
        Require(Execute(afterLoop, x, 7, y, 0) == 0, "完整传播后的循环退出值");
        Compare("自环上的常量输入", () => Loop(true), 1);
        var exceptional = Diamond(Eq(x, 0), true);
        var entry = exceptional.EntryBlock;
        var merge = exceptional.Blocks.Single(b => b.Start == 0x3000);
        entry.Handler = merge;
        entry.Successors.Add(merge); merge.Predecessors.Add(entry);
        var exceptionalPhi = (Phi)merge.Statements[0];
        merge.Statements[0] = exceptionalPhi with { Sources = [.. exceptionalPhi.Sources, x] };
        Require(EdgeConstants.Run(exceptional) == 1 && ((Phi)merge.Statements[0]).Sources[^1] == x,
            "正常边的事实不得替换同一前驱的异常输入");
        Require(SsaCheck.Verify(exceptional, Dominators.Compute(exceptional)).Count == 0, "异常输入保留 SSA");
        Console.WriteLine($"条件边常量差分检查通过：{checkedInputs} 组输入，含边方向、位宽、浮点、SSA 版本、重边和循环");
        if (binary is not null && metadata is not null) GateBranchCheck.Run(new RecoverySession(ModelCheck.Load(binary, metadata)));
        return 0;
    }

    private static MachineFunction Graph(params Block[] blocks)
    {
        foreach (var block in blocks)
        {
            ulong[] targets = block.Statements.Last() switch { Branch b => [b.Target, b.Fallthrough], Jump j => [j.Target], _ => [] };
            foreach (var address in targets)
            {
                var next = blocks.Single(b => b.Start == address);
                block.Successors.Add(next); next.Predecessors.Add(block);
            }
        }
        var result = new MachineFunction { Entry = blocks[0].Start, Range = new FunctionRange(0x1000, 0x4000, BoundaryEvidence.SymbolCandidate, "条件边差分"), Blocks = [.. blocks] };
        result.Renumber();
        return result;
    }

    private static ulong Execute(MachineFunction function, Variable x, ulong a, Variable y, ulong b)
    {
        var values = new Dictionary<Variable, ulong> { [x] = a, [y] = b };
        var evaluator = new Evaluator();
        ulong Eval(Expr expression)
        {
            var result = (ulong)evaluator.Eval(ExprMap.Map(expression, e => e is Use u ? Expr.C(values[u.Variable], u.Width) : null));
            Require(evaluator.Failure is null, evaluator.Failure ?? "");
            return result;
        }
        var block = function.EntryBlock;
        var incoming = -1;
        for (var step = 0; step < 100; step++)
        {
            var copies = block.Statements.OfType<Phi>().Select(p => (p.Target, Value: values[p.Sources[incoming]])).ToArray();
            foreach (var copy in copies) values[copy.Target] = copy.Value;
            var side = -1;
            foreach (var statement in block.Statements)
            {
                switch (statement)
                {
                    case Phi: break;
                    case Define d: values[d.Target] = Eval(d.Value); break;
                    case Branch branch: side = Eval(branch.Condition) != 0 ? 0 : 1; break;
                    case Jump: side = 0; break;
                    case Return { Value: { } value }: return Eval(value);
                    default: throw new NotSupportedException(statement.ToString());
                }
            }
            Require(side >= 0, "检查 CFG 缺少终结语句");
            var next = block.Successors[side];
            var occurrence = block.Successors.Take(side).Count(successor => successor == next);
            incoming = Enumerable.Range(0, next.Predecessors.Count).Where(i => next.Predecessors[i] == block).ElementAt(occurrence);
            block = next;
        }
        throw new InvalidOperationException("检查 CFG 超过预期迭代数");
    }

    private static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }
}
