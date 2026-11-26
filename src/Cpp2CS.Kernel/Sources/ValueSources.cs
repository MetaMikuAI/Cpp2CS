using System.Collections.Immutable;
using Cpp2CS.Snapshot;

namespace Cpp2CS.Kernel.Sources;

/// <summary>值的一个备选来源。块参数的备选带入边的身份；选择项的备选带条件与方向。</summary>
public readonly record struct Alternative(EdgeId? Edge, Term? Condition, bool Polarity, Term Value);

/// <summary>沿路径成立的一条文字的种类。</summary>
public enum LiteralKind : byte
{
    /// <summary>1 位的条件取 Value（1 或 0）。</summary>
    Condition,
    /// <summary>跳转表的选择子等于 Value。</summary>
    Selector,
    /// <summary>跳转表的选择子不等于前 Value 个取值中的任何一个。</summary>
    SelectorDefault,
    /// <summary>带展开出口的调用正常返回。</summary>
    InvokeNormal,
    /// <summary>带展开出口的调用经展开离开。</summary>
    InvokeUnwind,
}

/// <summary>沿一条边或一个选择条件成立的文字。项已经换到所在路径（或情况）的取值上。</summary>
public readonly record struct PathLiteral(LiteralKind Kind, Term? Term, long Value, OccurrenceId Occurrence)
{
    public override string ToString() => Kind switch
    {
        LiteralKind.Condition => $"{Term} = {Value}",
        LiteralKind.Selector => $"{Term} = {Value}",
        LiteralKind.SelectorDefault => $"{Term} ∉ [0, {Value})",
        LiteralKind.InvokeNormal => $"{Occurrence} 正常返回",
        _ => $"{Occurrence} 展开",
    };
}

/// <summary>
/// 情况：分情况得到的表的一行。Edges 是这一行选定的入边，从程序点向后依次列出；
/// Conditions 是这一行选定的选择条件；Terms 是所求各项在这一行的取值，不再含展开范围内的合流。
/// 已选定的条件（不含未定义的位时）在这一行的各项与其余条件里都换成它的取值。
/// Origin 是展开停下的块：各项只含这个块的参数与结果，以及沿途各块的结果。
/// </summary>
public sealed record Case(BlockId Origin, ImmutableArray<EdgeId> Edges, ImmutableArray<PathLiteral> Conditions, ImmutableArray<Term> Terms);

/// <summary>分情况的结果。各情况互斥，Complete 为真时合起来覆盖到达该点的全部路径。</summary>
public sealed record CaseTable(ImmutableArray<Case> Cases, bool Complete, int Steps);

/// <summary>走查的窗口：一组入口点和一组出口点，其间无环。</summary>
public sealed record Window(ImmutableArray<ProgramPoint> Entries, ImmutableArray<ProgramPoint> Exits);

/// <summary>一条路径的结束方式。</summary>
public enum PathEnd : byte { Exit, Return, NoReturn, Trap }

/// <summary>路径上经过的一个出现，以及它的各操作数在这条路径上的取值。</summary>
public sealed record PathStep(OccurrenceId Occurrence, ImmutableArray<Term> Operands);

/// <summary>
/// 窗口里的一条路径。各项都换到路径入口的取值上：只含入口所在块的参数、入口参数，以及沿途各出现的结果。
/// </summary>
public sealed record WalkPath(ProgramPoint Entry, ImmutableArray<EdgeId> Edges, ImmutableArray<PathStep> Steps,
    ImmutableArray<PathLiteral> Conditions, PathEnd End, ProgramPoint ExitPoint, ImmutableArray<Term> Outcome);

public enum WalkStatus : byte
{
    Complete,
    /// <summary>入口与出口之间有环。</summary>
    Cyclic,
    /// <summary>步数预算耗尽。</summary>
    Budget,
}

public sealed record WalkResult(WalkStatus Status, ImmutableArray<WalkPath> Paths, int Steps, EdgeId? CycleEdge);

/// <summary>逐情况提升的一行：这个情况，以及规则在这个情况上的结果。</summary>
public sealed record LiftedCase<T>(Case Case, T? Result);

/// <summary>逐情况提升的结果。Unanimous 为真时，各情况的结果相同，Value 就是这个结果。</summary>
public sealed record Lifted<T>(ImmutableArray<LiftedCase<T>> Cases, bool Complete, bool Unanimous, T? Value);

/// <summary>
/// 值的来源与合流的唯一解释。合流只在这里的三个操作里被解释：按边代入、分情况、走查。
/// 其余代码不拿入边，不遍历来源图去得出结论：入边与来源关系只在内核里可见。
///
/// 查询的输入须是这张图的项：来自图的项池；带本图图号的参数与结果须是图里的那个项（位宽、序号都对得上）。
/// 程序点须在图里。不满足时抛出 <see cref="ArgumentException"/>。
/// </summary>
public sealed class ValueSources
{
    public IFlowGraph Graph { get; }
    public TermPool Terms { get; }
    public FlowShape Shape { get; }

    public ValueSources(IFlowGraph graph, TermPool terms)
    {
        if (!ReferenceEquals(graph.Terms, terms)) throw new ArgumentException("项池须是图的项池");
        Graph = graph;
        Terms = terms;
        Shape = new FlowShape(graph);
    }

    // ---- 输入的核对 ----

    private void CheckPoint(ProgramPoint point)
    {
        if ((uint)point.Block.Index >= (uint)Graph.BlockCount || point.Index < 0 || point.Index > Graph.OccurrenceCount(point.Block))
            throw new ArgumentException($"程序点 {point} 不在图里");
    }

    private Exit CheckEdge(EdgeId edge)
    {
        if ((uint)edge.Source.Index >= (uint)Graph.BlockCount || (uint)edge.Exit >= (uint)Graph.Terminator(edge.Source).Exits.Length)
            throw new ArgumentException($"边 {edge} 不在图里");
        return Graph.Terminator(edge.Source).Exits[edge.Exit];
    }

    /// <summary>带本图图号的参数、结果是不是图里的那个项。</summary>
    private bool Genuine(Term t) => t.Kind switch
    {
        TermKind.EntryParameter => Graph.EntryParameters.Contains(t),
        TermKind.BlockParameter => (uint)t.Block.Index < (uint)Graph.BlockCount && (uint)t.ParameterIndex < (uint)Graph.Parameters(t.Block).Length
            && ReferenceEquals(Graph.Parameters(t.Block)[t.ParameterIndex], t),
        TermKind.Result => (uint)t.Block.Index < (uint)Graph.BlockCount && (uint)t.Occurrence.Index < (uint)Graph.OccurrenceCount(t.Block)
            && (uint)t.ResultIndex < (uint)Graph.Results(t.Occurrence).Length && ReferenceEquals(Graph.Results(t.Occurrence)[t.ResultIndex], t),
        _ => true,
    };

    /// <summary>
    /// 核对一组输入项。at 给出时，项还须在该程序点之前已经产生：不能含这个块里此点及之后的出现的结果。
    /// 别的块的结果按沿途的取值看待（走查给出的路径上的取值），不在此列。
    /// </summary>
    private void CheckTerms(IEnumerable<Term> terms, ProgramPoint? at)
    {
        var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
        void Visit(Term t)
        {
            if (!seen.Add(t)) return;
            if (!Terms.Owns(t)) throw new ArgumentException($"项 {t} 来自别的项池");
            if (t.Kind is TermKind.EntryParameter or TermKind.BlockParameter or TermKind.Result && t.Graph == Graph.Graph)
            {
                if (!Genuine(t)) throw new ArgumentException($"项 {t} 不是图里的参数或结果");
                if (at is { } point && t.Kind == TermKind.Result && t.Block == point.Block && t.Occurrence.Index >= point.Index)
                    throw new ArgumentException($"在 {point} 处，{t} 尚未产生");
            }
            foreach (var operand in t.Operands) Visit(operand);
        }
        foreach (var term in terms) Visit(term);
    }

    // ---- 来源关系 ----

    /// <summary>
    /// 一个值的备选来源。块参数：各条入边上对应位置的实参，保留回边、并行边与重复实参。
    /// 选择项：两支，各带条件与方向。其余的值没有备选。只在内核里使用。
    /// </summary>
    internal ImmutableArray<Alternative> Alternatives(Term value)
    {
        CheckTerms([value], null);
        if (value.Kind == TermKind.BlockParameter && value.Graph == Graph.Graph)
        {
            var edges = Shape.InEdges(value.Block);
            var result = ImmutableArray.CreateBuilder<Alternative>(edges.Length);
            foreach (var edge in edges)
                result.Add(new(edge, null, true, Graph.Terminator(edge.Source).Exits[edge.Exit].Arguments[value.ParameterIndex]));
            return result.MoveToImmutable();
        }
        if (value.Kind == TermKind.Select)
            return [new(null, value.Operands[0], true, value.Operands[1]), new(null, value.Operands[0], false, value.Operands[2])];
        return [];
    }

    // ---- 重写 ----

    private Term Rewrite(Term term, Dictionary<Term, Term> memo, Func<Term, Term?> replace)
    {
        if (memo.TryGetValue(term, out var known)) return known;
        Term result = replace(term) ?? term;
        if (ReferenceEquals(result, term) && term.Operands.Length > 0)
        {
            var operands = new Term[term.Operands.Length];
            bool changed = false;
            for (int i = 0; i < operands.Length; i++)
            {
                operands[i] = Rewrite(term.Operands[i], memo, replace);
                changed |= !ReferenceEquals(operands[i], term.Operands[i]);
            }
            if (changed) result = Terms.Rebuild(term, operands);
        }
        memo[term] = result;
        return result;
    }

    private Dictionary<Term, Term> NewMemo() => new(ReferenceEqualityComparer.Instance);

    // ---- 按边代入 ----

    /// <summary>
    /// 按边代入：把项里属于这条边的目标块的参数，同时换成这条边上的整行实参。
    /// 结果是源块里的值：只含源块的参数与结果，以及目标块自己的结果。
    /// </summary>
    public Term Substitute(EdgeId edge, Term term) => Substitute(edge, [term])[0];

    public ImmutableArray<Term> Substitute(EdgeId edge, ImmutableArray<Term> terms)
    {
        var exit = CheckEdge(edge);
        if (exit.Kind != ExitKind.Target) throw new ArgumentException($"{edge} 不去往块");
        CheckTerms(terms, null);
        return SubstituteRow(exit, terms);
    }

    /// <summary>按边代入，不核对输入：分情况内部使用，输入已经核对过。</summary>
    private ImmutableArray<Term> SubstituteRow(Exit exit, ImmutableArray<Term> terms)
    {
        var row = exit.Arguments;
        int graph = Graph.Graph, target = exit.Target.Index;
        var memo = NewMemo();
        Term? Replace(Term t) =>
            t.Kind == TermKind.BlockParameter && t.Graph == graph && t.Block.Index == target ? row[t.ParameterIndex] : null;
        var result = ImmutableArray.CreateBuilder<Term>(terms.Length);
        foreach (var term in terms) result.Add(Rewrite(term, memo, Replace));
        return result.MoveToImmutable();
    }

    // ---- 分情况 ----

    private static bool Mentions(Term term, int graph, int block, HashSet<Term> seen)
    {
        if (!seen.Add(term)) return false;
        if (term.Kind == TermKind.BlockParameter) return term.Graph == graph && term.Block.Index == block;
        foreach (var operand in term.Operands)
            if (Mentions(operand, graph, block, seen)) return true;
        return false;
    }

    /// <summary>找一个条件里不含选择的选择项。</summary>
    private static Term? InnermostSelect(Term term, HashSet<Term> seen)
    {
        if (!seen.Add(term)) return null;
        foreach (var operand in term.Operands)
            if (InnermostSelect(operand, seen) is { } inner) return inner;
        return term.Kind == TermKind.Select ? term : null;
    }

    /// <summary>
    /// 分情况：给定一个程序点和若干项，沿入边与选择条件向后展开，得到有限张情况表。
    /// 展开在三处停下：项里不再有所在块的参数；到达入口块；到达循环头——循环头的参数保留为原子，
    /// 表示“这一次迭代的值”。预算按步数计，耗尽时 Complete 为假。
    /// </summary>
    public CaseTable SplitCases(ProgramPoint point, ImmutableArray<Term> terms, int budget = 4096)
    {
        CheckPoint(point);
        CheckTerms(terms, point);
        var cases = ImmutableArray.CreateBuilder<Case>();
        int steps = 0;
        bool complete = true;
        var edges = new List<EdgeId>();

        void Expand(BlockId block, ImmutableArray<Term> values, ImmutableArray<PathLiteral> conditions)
        {
            if (++steps > budget) { complete = false; return; }
            // 代入之后，条件可能变成常量或互相矛盾：矛盾的情况不存在，已经成立的条件不必再列。
            // 代入还可能让已选定的条件与各项里的某个子项成为同一个项：把它换成选定的取值，再整理，直到不再变化。
            if (Settle(values, conditions) is not { } settled) return;
            (values, conditions) = settled;

            // 先按选择条件分。条件取定之后，同一个条件上的所有选择一起化简。
            var seen = new HashSet<Term>(ReferenceEqualityComparer.Instance);
            Term? select = null;
            foreach (var value in values)
                if ((select = InnermostSelect(value, seen)) is not null) break;
            if (select is null)
                foreach (var condition in conditions)
                    if (condition.Term is not null && (select = InnermostSelect(condition.Term, seen)) is not null) break;
            if (select is not null)
            {
                var test = select.Operands[0];
                foreach (bool polarity in (ReadOnlySpan<bool>)[true, false])
                {
                    var memo = NewMemo();
                    Term constant = polarity ? Terms.True : Terms.False;
                    Term? Replace(Term t) => ReferenceEquals(t, test) ? constant : null;
                    var next = ImmutableArray.CreateBuilder<Term>(values.Length);
                    foreach (var value in values) next.Add(Rewrite(value, memo, Replace));
                    var nextConditions = ImmutableArray.CreateBuilder<PathLiteral>(conditions.Length + 1);
                    foreach (var condition in conditions)
                        nextConditions.Add(condition.Term is null ? condition : condition with { Term = Rewrite(condition.Term, memo, Replace) });
                    nextConditions.Add(new(LiteralKind.Condition, test, polarity ? 1 : 0, default));
                    Expand(block, next.MoveToImmutable(), nextConditions.ToImmutable());
                }
                return;
            }

            // 再按入边分。
            int graph = Graph.Graph;
            seen.Clear();
            bool merged = false;
            foreach (var value in values) merged |= Mentions(value, graph, block.Index, seen);
            foreach (var condition in conditions)
                if (condition.Term is not null) merged |= Mentions(condition.Term, graph, block.Index, seen);
            if (!merged || block == Graph.Entry || Shape.IsLoopHead(block))
            {
                cases.Add(new Case(block, [.. edges], conditions, values));
                return;
            }
            foreach (var edge in Shape.InEdges(block))
            {
                var conditionTerms = ImmutableArray.CreateBuilder<Term>(values.Length + conditions.Length);
                conditionTerms.AddRange(values);
                foreach (var condition in conditions) conditionTerms.Add(condition.Term ?? Terms.False);
                var substituted = SubstituteRow(Graph.Terminator(edge.Source).Exits[edge.Exit], conditionTerms.ToImmutable());
                var nextConditions = ImmutableArray.CreateBuilder<PathLiteral>(conditions.Length);
                for (int i = 0; i < conditions.Length; i++)
                    nextConditions.Add(conditions[i].Term is null ? conditions[i] : conditions[i] with { Term = substituted[values.Length + i] });
                edges.Add(edge);
                Expand(edge.Source, substituted[..values.Length], nextConditions.MoveToImmutable());
                edges.RemoveAt(edges.Count - 1);
            }
        }

        Expand(point.Block, terms, []);
        return new CaseTable(cases.ToImmutable(), complete, steps);
    }

    /// <summary>
    /// 把已选定的条件代入各项与其余条件，并整理条件，直到不再变化；条件互相矛盾时返回空。
    /// 条件的项含未定义的位时不代入：同一个未定义的项可以代表互不相关的位（设计 7.2）。
    /// </summary>
    private (ImmutableArray<Term> Values, ImmutableArray<PathLiteral> Conditions)? Settle(ImmutableArray<Term> values, ImmutableArray<PathLiteral> conditions)
    {
        for (int round = 0; ; round++)
        {
            if (Simplify(conditions) is not { } simplified) return null;
            conditions = simplified;
            var known = new Dictionary<Term, Term>(ReferenceEqualityComparer.Instance);
            foreach (var condition in conditions)
                if (condition.Kind == LiteralKind.Condition && condition.Term is { HasUndefined: false } term)
                    known[term] = condition.Value != 0 ? Terms.True : Terms.False;
            if (known.Count == 0 || round > conditions.Length) return (values, conditions);
            bool changed = false;
            var memo = NewMemo();
            Term? Replace(Term t) => known.TryGetValue(t, out var constant) ? constant : null;
            var nextValues = ImmutableArray.CreateBuilder<Term>(values.Length);
            foreach (var value in values)
            {
                var next = Rewrite(value, memo, Replace);
                changed |= !ReferenceEquals(next, value);
                nextValues.Add(next);
            }
            var nextConditions = ImmutableArray.CreateBuilder<PathLiteral>(conditions.Length);
            foreach (var condition in conditions)
            {
                // 条件自己的项不换成自己的取值，只换其中别的已选定条件。
                if (condition.Term is not { } term) { nextConditions.Add(condition); continue; }
                var own = known.Remove(term, out var saved);
                var next = Rewrite(term, NewMemo(), Replace);
                if (own) known[term] = saved!;
                changed |= !ReferenceEquals(next, term);
                nextConditions.Add(condition with { Term = next });
            }
            if (!changed) return (values, conditions);
            values = nextValues.MoveToImmutable();
            conditions = nextConditions.MoveToImmutable();
        }
    }

    /// <summary>
    /// 整理一组条件：取反的条件改写成对原条件的相反取值；常量条件成立的删去、不成立的说明这一组不可能同时成立（返回空）；
    /// 同一个条件重复的只留一个，取值相反的同样返回空。
    /// </summary>
    private static ImmutableArray<PathLiteral>? Simplify(ImmutableArray<PathLiteral> conditions)
    {
        var chosen = new Dictionary<Term, long>(ReferenceEqualityComparer.Instance);
        var result = ImmutableArray.CreateBuilder<PathLiteral>(conditions.Length);
        foreach (var condition in conditions)
        {
            if (condition.Kind != LiteralKind.Condition || condition.Term is null) { result.Add(condition); continue; }
            Term term = condition.Term;
            long value = condition.Value;
            while (term.Kind == TermKind.Operation && term.Op == Op.Not) { term = term.Operands[0]; value = 1 - value; }
            if (term.Kind == TermKind.Constant)
            {
                if ((term.IsZero ? 0 : 1) != value) return null;
                continue;
            }
            if (chosen.TryGetValue(term, out long known))
            {
                if (known != value) return null;
                continue;
            }
            chosen.Add(term, value);
            result.Add(new(LiteralKind.Condition, term, value, default));
        }
        return result.ToImmutable();
    }

    // ---- 逐情况提升 ----

    /// <summary>
    /// 逐情况提升：把一条写给“输入不是合流”的规则，对每个情况各用一次。规则看不到合流。
    /// 各情况的结果相同时，Value 就是这个结果。
    /// </summary>
    public Lifted<T> Lift<T>(ProgramPoint point, Term input, Func<Term, T?> rule, int budget = 4096) where T : class
    {
        var table = SplitCases(point, [input], budget);
        var rows = ImmutableArray.CreateBuilder<LiftedCase<T>>(table.Cases.Length);
        T? common = null;
        bool unanimous = table.Complete && table.Cases.Length > 0;
        foreach (var item in table.Cases)
        {
            T? result = rule(item.Terms[0]);
            rows.Add(new(item, result));
            if (result is null) unanimous = false;
            else if (common is null) common = result;
            else if (!EqualityComparer<T>.Default.Equals(common, result)) unanimous = false;
        }
        return new Lifted<T>(rows.MoveToImmutable(), table.Complete, unanimous, unanimous ? common : null);
    }

    // ---- 走查 ----

    /// <summary>
    /// 走查：枚举窗口里从每个入口点到出口点或到结局的每条路径。每过一条边就按边代入，
    /// 给出路径上依次经过的出现、各操作数在这条路径上的取值和累积的路径条件。
    /// 从一个块的入口开始时，这个块的参数保留为原子。
    /// 入口与出口之间有环时返回 Cyclic；含环的区域由调用方在切点处切成无环的段。
    /// </summary>
    public WalkResult Walk(Window window, int budget = 65536)
    {
        foreach (var point in window.Entries) CheckPoint(point);
        foreach (var point in window.Exits) CheckPoint(point);
        var exits = new HashSet<ProgramPoint>(window.Exits);
        var paths = ImmutableArray.CreateBuilder<WalkPath>();
        var status = WalkStatus.Complete;
        EdgeId? cycle = null;
        int steps = 0;
        int graph = Graph.Graph;

        foreach (var entry in window.Entries)
        {
            var edges = new List<EdgeId>();
            var trace = new List<PathStep>();
            var conditions = new List<PathLiteral>();
            var entered = new HashSet<int>();
            if (entry.Index == 0) entered.Add(entry.Block.Index);

            void Finish(PathEnd end, ProgramPoint at, ImmutableArray<Term> outcome) =>
                paths.Add(new WalkPath(entry, [.. edges], [.. trace], [.. conditions], end, at, outcome));

            // row 为空表示所在块的参数保留为原子。
            void Visit(ProgramPoint from, ImmutableArray<Term> row, bool start)
            {
                if (status != WalkStatus.Complete) return;
                var block = from.Block;
                var memo = NewMemo();
                Term? Replace(Term t) => !row.IsDefault && t.Kind == TermKind.BlockParameter && t.Graph == graph
                    && t.Block == block ? row[t.ParameterIndex] : null;
                Term Value(Term t) => row.IsDefault ? t : Rewrite(t, memo, Replace);

                int count = Graph.OccurrenceCount(block), traced = trace.Count;
                for (int i = from.Index; i <= count; i++)
                {
                    var here = new ProgramPoint(block, i);
                    if (!(start && i == from.Index) && exits.Contains(here))
                    {
                        Finish(PathEnd.Exit, here, []);
                        trace.RemoveRange(traced, trace.Count - traced);
                        return;
                    }
                    if (i == count) break;
                    if (++steps > budget) { status = WalkStatus.Budget; return; }
                    var id = new OccurrenceId(block, i);
                    var operands = Graph.Operands(id);
                    var values = ImmutableArray.CreateBuilder<Term>(operands.Length);
                    foreach (var operand in operands) values.Add(Value(operand));
                    trace.Add(new PathStep(id, values.MoveToImmutable()));
                }

                var terminator = Graph.Terminator(block);
                var end = new ProgramPoint(block, count);
                Term? test = terminator.Condition is null ? null : Value(terminator.Condition);
                for (int e = 0; e < terminator.Exits.Length && status == WalkStatus.Complete; e++)
                {
                    if (++steps > budget) { status = WalkStatus.Budget; break; }
                    var exit = terminator.Exits[e];
                    int literals = conditions.Count;
                    switch (terminator.Kind)
                    {
                        case TerminatorKind.Branch:
                            conditions.Add(new(LiteralKind.Condition, test, e == 0 ? 1 : 0, default));
                            break;
                        case TerminatorKind.Switch:
                            conditions.Add(e < terminator.Exits.Length - 1
                                ? new(LiteralKind.Selector, test, e, default)
                                : new(LiteralKind.SelectorDefault, test, e, default));
                            break;
                        case TerminatorKind.Invoke:
                            conditions.Add(new(e == 0 ? LiteralKind.InvokeNormal : LiteralKind.InvokeUnwind, null, 0, new(block, count - 1)));
                            break;
                    }
                    var arguments = ImmutableArray.CreateBuilder<Term>(exit.Arguments.Length);
                    foreach (var argument in exit.Arguments) arguments.Add(Value(argument));
                    switch (exit.Kind)
                    {
                        case ExitKind.Target:
                        {
                            var edge = new EdgeId(block, e);
                            int target = exit.Target.Index;
                            edges.Add(edge);
                            if (exits.Contains(new(exit.Target, 0)))
                                Finish(PathEnd.Exit, new(exit.Target, 0), arguments.MoveToImmutable());
                            else if (!entered.Add(target))
                            {
                                status = WalkStatus.Cyclic;
                                cycle = edge;
                            }
                            else
                            {
                                Visit(new(exit.Target, 0), arguments.MoveToImmutable(), false);
                                entered.Remove(target);
                            }
                            edges.RemoveAt(edges.Count - 1);
                            break;
                        }
                        case ExitKind.Return:
                            Finish(PathEnd.Return, end, arguments.MoveToImmutable());
                            break;
                        case ExitKind.NoReturn:
                            Finish(PathEnd.NoReturn, end, []);
                            break;
                        default:
                            Finish(PathEnd.Trap, end, []);
                            break;
                    }
                    conditions.RemoveRange(literals, conditions.Count - literals);
                }
                trace.RemoveRange(traced, trace.Count - traced);
            }

            Visit(entry, default, true);
            if (status != WalkStatus.Complete) break;
        }
        return new WalkResult(status, paths.ToImmutable(), steps, cycle);
    }
}
