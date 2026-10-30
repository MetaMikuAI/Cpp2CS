using Cpp2CS.Facts;
using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;

namespace Cpp2CS.Idioms;

/// <summary>只消去已逐点配对的 C++ wrapper；失败时保留原来的三步及其异常边。</summary>
internal static class ManagedThrowNormalizer
{
    internal sealed record Match(Call Throw, Call? Allocate, Store? Write, Expr? Exception, string Reason)
    {
        public bool Proven => Reason == "命中";
    }

    public static Match[] Analyze(ProgramFacts facts, MachineFunction function)
    {
        var all = function.Blocks.SelectMany(b => b.Statements).ToArray();
        var values = all.OfType<Define>().ToDictionary(d => d.Target, d => d.Value);
        foreach (var (_, d) in function.Dead) values.TryAdd(d.Target, d.Value);
        Expr Root(Expr e, int depth = 32) => depth == 0 ? e : e switch
        {
            Use u when values.TryGetValue(u.Variable, out var v) => Root(v, depth - 1),
            Ir.Convert { Width: 64, Operand.Width: 64 } c => Root(c.Operand, depth - 1),
            Binary { Op: BinOp.Add, Right: Const { Value: 0 } } b => Root(b.Left, depth - 1),
            _ => e,
        };
        var matches = new List<Match>();
        foreach (var block in function.Blocks)
            foreach (var call in block.Statements.OfType<Call>().Where(c => c.Op is { Kind: OpKind.Import, Operand: "__cxa_throw" }))
            {
                Match Fail(string reason) => new(call, null, null, null, reason);
                if (call.Arguments.Length < 3 || Root(call.Arguments[1]) is not Const type ||
                    ExceptionFacts.TypeName(facts.Model.Image, type.Value) != ExceptionFacts.WrapperName ||
                    Root(call.Arguments[2]) is not Const { Value: 0 })
                { matches.Add(Fail("残余/RTTI或析构器")); continue; }
                var wrapper = Root(call.Arguments[0]);
                if (wrapper is not Use { Width: 64 } use)
                { matches.Add(Fail("残余/分配结果非SSA根")); continue; }
                var allocate = all.OfType<Call>().SingleOrDefault(c => c.Defines.Contains(use.Variable));
                if (allocate is not { Op.Kind: OpKind.Import, Op.Operand: "__cxa_allocate_exception" } ||
                    allocate.Defines.FirstOrDefault() != use.Variable || allocate.Arguments.Length == 0 || Root(allocate.Arguments[0]) is not Const { Value: 8 })
                { matches.Add(Fail("残余/非allocate8")); continue; }
                Store? write = null;
                var current = block;
                var index = block.Statements.IndexOf(call);
                var seen = new HashSet<Block>();
                var paired = false;
                var stopped = false;
                while (seen.Add(current))
                {
                    for (var i = index - 1; i >= 0; i--)
                    {
                        var statement = current.Statements[i];
                        if (ReferenceEquals(statement, allocate)) { paired = write is not null; stopped = true; break; }
                        if (statement is Store s)
                        {
                            if (write is not null || s.Value.Width != 64 || Root(s.Target) != wrapper) { stopped = true; break; }
                            write = s;
                        }
                        else if (statement is not (Define or Phi or Jump or Nop)) { stopped = true; break; }
                    }
                    if (stopped) break;
                    if (current.IsLandingPad || current.Predecessors is not [var previous] || previous.NormalSuccessors.ToArray() is not [var only] || only != current) break;
                    current = previous;
                    index = current.Statements.Count;
                }
                if (!paired || write is null)
                { matches.Add(Fail("残余/分配写入非唯一路径")); continue; }
                // 分配结果不能逃逸。仅放行 SSA 别名、该次 +0 写入和该次 throw 的 ABI 读取。
                var escaped = all.Any(s => !ReferenceEquals(s, call) && !ReferenceEquals(s, write) &&
                    (s is Phi p ? p.Sources.Any(v => Root(new Use(v, v.Width)) == wrapper)
                    : !(s is Define d && Root(d.Value) == wrapper) && ExprMap.Operands(s).SelectMany(ExprMap.Walk).OfType<Use>().Any(u => Root(new Use(u.Variable, u.Variable.Width)) == wrapper)));
                if (escaped || ExprMap.Walk(write.Value).OfType<Use>().Any(u => Root(new Use(u.Variable, u.Variable.Width)) == wrapper))
                { matches.Add(Fail("残余/wrapper逃逸")); continue; }
                matches.Add(new(call, allocate, write, write.Value, "命中"));
            }
        return matches.ToArray();
    }

    public static bool Run(ProgramFacts facts, MachineFunction function, IdiomResult report)
    {
        var changed = false;
        foreach (var match in Analyze(facts, function).Where(m => m.Proven))
        {
            foreach (var block in function.Blocks)
            {
                for (var i = 0; i < block.Statements.Count; i++)
                {
                    var s = block.Statements[i];
                    if (ReferenceEquals(s, match.Throw)) block.Statements[i] = match.Throw with
                    { Op = new(OpKind.ThrowManaged, null), Arguments = [match.Exception!], Sources = [], Results = [], Defines = [] };
                    else if (ReferenceEquals(s, match.Allocate) || ReferenceEquals(s, match.Write))
                        block.Statements[i] = new Nop(s.Address, "已配对的托管异常wrapper");
                }
                // allocate_exception 失败按 ABI 终止进程，不抛托管异常；消去的只是它自己的异常边。
                if (block.Handler is not null && !block.Statements.OfType<Call>().Any() &&
                    match.Allocate!.Address >= block.Start && match.Allocate.Address < block.End)
                    MachineFunction.RemoveEdgeAt(block, block.Successors.Count - 1);
            }
            report.Hit(Template.ManagedThrow);
            changed = true;
        }
        return changed;
    }
}
