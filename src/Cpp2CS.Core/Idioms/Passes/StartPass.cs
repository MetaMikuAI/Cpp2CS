using Cpp2CS.Machine.Flow;
using Cpp2CS.Ir;
using static Cpp2CS.Idioms.IdiomState;

namespace Cpp2CS.Idioms;

internal static class StartPass
{
    internal static Point Start(this IdiomState state, Block head, params Expr[] extra) => state.Start(head, head.Statements.Count - 1, extra);
    internal static Point Start(this IdiomState state, Block head, int end, params Expr[] extra)
    {
        var statements = head.Statements;
        var endAddress = end < statements.Count ? statements[end].Address : statements.Count > 0 ? statements[^1].Address + 1 : head.Start;
        var defined = new Dictionary<Variable, int>();
        for (var i = 0; i < end; i++)
            if (statements[i] is Define d)
                defined[d.Target] = i;
        var start = end;
        var seen = new HashSet<Variable>();
        var roots = (end < statements.Count ? ExprMap.Operands(statements[end]) : []).Concat(extra).ToList();
        var work = new Stack<Expr>(roots);
        while (work.Count > 0)
            foreach (var use in ExprMap.Walk(work.Pop()).OfType<Use>())
                if (seen.Add(use.Variable) && defined.TryGetValue(use.Variable, out var i))
                {
                    start = Math.Min(start, i);
                    work.Push(((Define)statements[i]).Value);
                }

        var address = start < statements.Count ? statements[start].Address : endAddress;
        var inlined = roots.Select(e => state.defs.Expand(e)).SelectMany(ExprMap.Walk).ToHashSet();
        // 删去的定义只看最后一次调用或写内存之后的：更早的同一表达式（如两次虚调用各自读 klass）未必是这里用到的值
        var barrier = statements.Take(Math.Min(end, statements.Count)).Where(x => x is Call or Store && x.Address >= head.Start && x.Address < endAddress).Select(x => x.Address).DefaultIfEmpty(head.Start).Max();
        Define? flags = null;
        foreach (var (block, d) in state.function.Dead)
        {
            if (block != head || d.Address < head.Start || d.Address >= endAddress || d.Address <= barrier && barrier != head.Start)
                continue;
            if (d.Target.Storage.Bank == Bank.Flags)
            {
                if (flags is null || d.Address > flags.Address)
                    flags = d;
            }
            // 只看有运算的定义：常量、复制之类处处可能作为子表达式出现，而且由前缀执行与 env 重建
            else if (state.defs.Expand(new Use(d.Target, d.Target.Width)) is not (Const or Use or Symbol or FrameAddress) and var value && inlined.Contains(value))
                address = Math.Min(address, d.Address);
        }

        if (end < statements.Count && statements[end] is Branch && flags is not null && !statements.Take(end).Any(x => x.Address > flags.Address && x is Define { Target.Storage.Bank: Bank.Flags }))
            address = Math.Min(address, flags.Address);
        var first = statements.TakeWhile(x => x is Phi).Count();
        if (address < head.Start || address > endAddress)
            return new(first, head.Start);
        var index = statements.FindIndex(x => x is not Phi && x.Address >= address);
        if (index < 0 || index > start)
            index = start;
        return index <= first && (first == statements.Count || address <= statements[first].Address) ? new(first, head.Start) : new(index, address);
    }
}
