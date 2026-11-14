using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Recovery.Structure;

namespace Cpp2CS.Recovery.Exceptions;

public sealed record FinallyPlan(BlockIdentity Entry, ImmutableHashSet<BlockIdentity> Body,
    BlockIdentity Completion, BlockIdentity Continuation, ImmutableHashSet<BlockIdentity> Removed,
    ImmutableHashSet<BlockIdentity> Arrivals, ImmutableDictionary<Term, Term> Values)
{
    public BlockIdentity? PropagatesTo { get; init; }
    public ImmutableDictionary<BlockIdentity, BlockIdentity> Branches { get; init; } = ImmutableDictionary<BlockIdentity, BlockIdentity>.Empty;
    public ImmutableDictionary<BlockIdentity, BlockIdentity> LeaveTargets { get; init; } = ImmutableDictionary<BlockIdentity, BlockIdentity>.Empty;
    public ImmutableHashSet<Statement> Omitted { get; init; } = [];
    public ImmutableHashSet<BlockIdentity> Unreachable { get; init; } = [];
}

public sealed partial class ExceptionRegionQuery
{
    private IEnumerable<Term> SemanticEndUses(Terminator end) => end is Return returned && names.EntrySignature is { } signature
        ? returned.Results.Where(value => signature.Slots.Return.Pieces.Any(piece => piece.Slot == value.Slot)).Select(value => value.Value)
        : SnapshotRewrite.Uses(end);

    private FinallyPlan? SharedFinally(QueryContext c, BlockIdentity handler, HashSet<BlockIdentity> capture,
        Dictionary<CallIdentity, ClassifiedCall> classified, Func<Statement, bool> privateStatement, Dictionary<CallIdentity, BlockIdentity?> unwind)
    {
        var f = c.Snapshot; var blocks = f.Blocks.ToDictionary(b => b.Identity);
        var normalFlow = new FlowQueries(includeUnwind: false);
        bool Dominates(BlockIdentity a, BlockIdentity b) => c.Get(normalFlow.Dominates, new(a, b)) is { IsSuccess: true, Value: true };
        if (capture.Any(id => !blocks[id].Statements.All(privateStatement) || blocks[id].End is not Jump)) return null;
        var exits = capture.SelectMany(id => SnapshotRewrite.Targets(blocks[id].End)).Where(id => !capture.Contains(id)).Distinct().ToArray();
        if (exits.Length != 1) return null;
        var entry = blocks[exits[0]];
        bool Caught(Term value) => c.Get(names, value) is { IsSuccess: true, Value.Name: CaughtExceptionName caught } && caught.Handler == handler;
        Term Resolve(Term value) => c.Get(state.Resolve, value) is { IsSuccess: true } answer ? answer.Value : value;
        IEnumerable<Term> Uses(Statement statement) => statement switch
        {
            Call call => (classified[call.Identity].Inputs?.Values.SelectMany(v => v.Source is TermSource t ? new[] { t.Term } : [])
                ?? SnapshotRewrite.Uses(call)).Concat(call.Target is ComputedTarget target ? [target.Value] : []).Select(Resolve),
            MemoryRead read => new[] { Resolve(read.Address) },
            _ => SnapshotRewrite.Uses(statement).Select(Resolve),
        };
        var live = new StructureLiveness(f, end => SemanticEndUses(end).Select(Resolve), statementUses: Uses);
        var arrivals = entry.Merges.SelectMany(m => m.Inputs).Select(i => i.Predecessor).Where(id => !capture.Contains(id)).ToImmutableHashSet();
        if (arrivals.IsEmpty) return null;
        foreach (var saved in entry.Merges)
        {
            if (!saved.Inputs.Any(i => capture.Contains(i.Predecessor) && Caught(i.Value))
                || saved.Inputs.Any(i => capture.Contains(i.Predecessor) ? !Caught(i.Value) : Resolve(i.Value).ConstantValue != 0)) continue;
            foreach (var test in f.Blocks.Where(b => b.End is Branch))
            {
                var condition = Resolve(((Branch)test.End).Condition);
                var nonzero = f.Terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, saved.Result, f.Terms.Constant(0, saved.Result.Width));
                var zero = f.Terms.Apply(new CoreOperator(CoreOperation.Equal), 1, saved.Result, f.Terms.Constant(0, saved.Result.Width));
                var notZero = f.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, zero);
                var notNonzero = f.Terms.Apply(new CoreOperator(CoreOperation.Not), 1, nonzero);
                bool positive = condition == nonzero || condition == notZero;
                if (!positive && condition != zero && condition != notNonzero) continue;
                var branch = (Branch)test.End;
                var thrown = blocks[positive ? branch.True : branch.False];
                var continuation = positive ? branch.False : branch.True;
                var events = thrown.Statements.Where(s => !privateStatement(s)).ToArray();
                if (events is not [Call call] || classified[call.Identity].Operation?.Name != "Rethrow"
                    || classified[call.Identity].Inputs?.GetValueOrDefault("exception")?.Source is not TermSource argument
                    || names.SameValue(c, argument.Term, saved.Result) is not { IsSuccess: true, Value: true }
                    || thrown.End is not Unreachable
                    || !live.OnlyAt(saved.Result, new HashSet<(BlockIdentity, bool)> { (test.Identity, true), (thrown.Identity, false) })) continue;
                var body = f.Blocks.Where(b => Dominates(entry.Identity, b.Identity)
                    && (b.Identity == test.Identity || !Dominates(test.Identity, b.Identity))).Select(b => b.Identity).ToImmutableHashSet();
                var branches = ImmutableDictionary.CreateBuilder<BlockIdentity, BlockIdentity>();
                IEnumerable<BlockIdentity> Targets(Block block)
                {
                    if (block.Identity != test.Identity && block.End is Branch decision
                        && c.Get(facts, new(new(block.Identity, block.Statements.Length), decision.Condition)) is { IsSuccess: true, Value: not PathTruth.Unknown } truth)
                    {
                        var target = truth.Value == PathTruth.True ? decision.True : decision.False;
                        branches[block.Identity] = target;
                        return [target];
                    }
                    return SnapshotRewrite.Targets(block.End);
                }
                if (!body.Contains(test.Identity) || body.Overlaps(capture)
                    || body.Any(id => id != test.Identity && (Targets(blocks[id]).Any(to => !body.Contains(to))
                        || blocks[id].End is Return or ResumeUnwind
                        || blocks[id].End is Unreachable && !blocks[id].Statements.OfType<Call>().Any(call => call.DoesNotReturn)))) continue;
                var index = c.Get(state.Index, 0);
                if (!index.IsSuccess || body.Any(id => id != entry.Identity && index.Value.Predecessors[id].Any(p => !body.Contains(p.Block)
                    && c.Get(normalFlow.Graph, 0).Value.Reachable.Contains(p.Block)))) continue;
                var aliases = ImmutableDictionary.CreateBuilder<Term, Term>(); bool valid = true;
                foreach (var merge in entry.Merges.Where(m => m != saved && live.Inside(m.Result, body)))
                {
                    var value = merge.Inputs.First(i => !capture.Contains(i.Predecessor)).Value;
                    if (value == merge.Result || merge.Inputs.Any(i => names.SameValue(c, value, i.Value) is not { IsSuccess: true, Value: true }))
                    { valid = false; break; }
                    aliases.Add(merge.Result, value);
                }
                if (!valid) continue;
                var removed = capture.Append(thrown.Identity).ToImmutableHashSet();
                var targets = ImmutableDictionary.CreateBuilder<BlockIdentity, BlockIdentity>();
                var dispatch = blocks[continuation];
                // 常量选择值只分派原 try 的正常出口；异常路径不会读取这个值。
                var dispatchValue = dispatch.End is Branch db ? db.Condition : dispatch.End is JumpTable dt ? dt.Selector : null;
                var selectors = dispatchValue is null ? [] : entry.Merges.Where(m => SnapshotRewrite.Dependencies([Resolve(dispatchValue)]).Contains(m.Result)).ToArray();
                if (selectors.Length != 0 && dispatch.End is Branch or JumpTable && dispatch.Statements.All(privateStatement)
                    && index.Value.Predecessors[continuation].All(p => p.Block == test.Identity))
                {
                    var selector = dispatch.End is Branch decision ? decision.Condition : ((JumpTable)dispatch.End).Selector;
                    var projected = new EdgeValueQuery(state); bool constants = true;
                    foreach (var from in arrivals)
                    {
                        var value = c.Get(projected, new(selector, new(from, entry.Identity)));
                        if (!value.IsSuccess || Resolve(value.Value).ConstantValue is not { } n) { constants = false; break; }
                        targets.Add(from, dispatch.End is Branch decision2 ? n == 0 ? decision2.False : decision2.True
                            : ((JumpTable)dispatch.End).Cases.FirstOrDefault(item => item.Value == n)?.Target ?? ((JumpTable)dispatch.End).Default);
                    }
                    if (!constants || selectors.Length == 0 || selectors.Any(m => !live.OnlyAt(m.Result,
                        new HashSet<(BlockIdentity, bool)> { (dispatch.Identity, true) }))
                        || targets.Values.Any(to => blocks[to].Merges.Any(m => m.Inputs.Any(input => input.Predecessor == dispatch.Identity)))) continue;
                    removed = removed.Add(dispatch.Identity);
                }
                return new(entry.Identity, body, test.Identity, continuation, removed, arrivals, aliases.ToImmutable())
                { LeaveTargets = targets.ToImmutable(), Branches = branches.ToImmutable(), PropagatesTo = unwind[call.Identity] };
            }
        }
        return null;
    }
}

public sealed partial class ExceptionRegionQuery
{
    private FinallyPlan? CopiedFinally(QueryContext c, ExceptionClausePlan clause, HashSet<BlockIdentity> protectedBlocks,
        Dictionary<CallIdentity, ClassifiedCall> classified, Func<Statement, bool> privateStatement,
        Dictionary<CallIdentity, BlockIdentity> rethrows, HashSet<BlockIdentity> removed, Dictionary<CallIdentity, BlockIdentity?> unwind, Dominance dominance)
    {
        var f = c.Snapshot; var blocks = f.Blocks.ToDictionary(b => b.Identity);
        var projection = new SnapshotRewrite(f);
        var branches = ImmutableDictionary.CreateBuilder<BlockIdentity, BlockIdentity>();
        foreach (var id in clause.Body)
            if (blocks[id].End is Branch branch && names.KnownCondition(c, branch.Condition) is { IsSuccess: true, Value.ConstantValue: { } n })
            {
                var target = n == 0 ? branch.False : branch.True;
                branches.Add(id, target); projection.Blocks[id] = blocks[id] with { End = new Jump(target) };
            }
        var projected = branches.Count == 0 ? f : projection.Apply();
        var retained = projected.Blocks.ToDictionary(b => b.Identity);
        var projectedIndex = ReferenceEquals(projected, f) ? c.Get(state.Index, 0) : names.CreateContext(projected).Get(state.Index, 0);
        if (!projectedIndex.IsSuccess) return null;
        // 直线清理逐语句复核；含分支或结果对应尚无共同执行凭据时保留展开形式。
        var body = clause.Body.Except(removed).Intersect(retained.Keys).ToImmutableHashSet();
        if (body.Any(id => retained[id].End is not (Jump or Unreachable)) || body.Count(id => retained[id].End is Unreachable) != 1) return null;
        bool Dominates(BlockIdentity a, BlockIdentity b) => a == b || dominance.StrictlyDominates(a, 0, b, 0);
        var chain = body.OrderBy(id => body.Count(other => Dominates(other, id)))
            .Select(id => blocks[id] with { End = retained[id].End }).ToArray();
        if (chain.Length == 0 || chain[0].Identity != clause.Entry || chain[^1].End is not Unreachable
            || chain.SkipLast(1).Where((block, i) => block.End is not Jump jump || jump.Target != chain[i + 1].Identity).Any()) return null;
        var operations = chain.SelectMany(block => block.Statements).Where(s => !privateStatement(s)).ToArray();
        if (operations.LastOrDefault() is not Call last || !rethrows.ContainsKey(last.Identity)) return null;
        operations = operations.SkipLast(1).ToArray();
        var outer = unwind[last.Identity];
        if (outer is not null && blocks[outer].Merges.Any(merge => merge.Inputs.Any(input => input.Predecessor == chain[^1].Identity))) return null;
        var exits = protectedBlocks.SelectMany(id => SnapshotRewrite.Targets(blocks[id].End)).Where(id => !protectedBlocks.Contains(id) && !removed.Contains(id)).Distinct().ToArray();
        if (exits.Length == 0) return null;
        bool Same(Term a, Term b) => names.SameValue(c, a, b) is { IsSuccess: true, Value: true };
        bool SameStatement(Statement a, Statement b)
        {
            if (a is MemoryWrite x && b is MemoryWrite y) return x.Width == y.Width && x.Release == y.Release && Same(x.Address, y.Address) && Same(x.Value, y.Value);
            if (a is not Call xcall || b is not Call ycall) return false;
            if (xcall.Target != ycall.Target && !(xcall.Target is ComputedTarget xt && ycall.Target is ComputedTarget yt && Same(xt.Value, yt.Value))) return false;
            var xnamed = classified[xcall.Identity]; var ynamed = classified[ycall.Identity];
            if (unwind[xcall.Identity] != unwind[ycall.Identity] || xcall.DoesNotReturn || ycall.DoesNotReturn || xnamed.Kind != ynamed.Kind || xnamed.Operation != ynamed.Operation) return false;
            if (xnamed.Kind == CallKind.Managed && (xnamed.Candidates is not { Failure: null } xc || ynamed.Candidates is not { Failure: null } yc
                || !xc.Candidates.Select(candidate => candidate.Entry).SequenceEqual(yc.Candidates.Select(candidate => candidate.Entry))
                || xc.Candidates.Concat(yc.Candidates).Any(candidate => !candidate.Binding.Success))) return false;
            var xb = xnamed.Binding is { } xbound ? new[] { xbound } : xnamed.Candidates?.Candidates.Select(candidate => candidate.Binding.Value!).ToArray() ?? [];
            var yb = ynamed.Binding is { } ybound ? new[] { ybound } : ynamed.Candidates?.Candidates.Select(candidate => candidate.Binding.Value!).ToArray() ?? [];
            if (xb.Length == 0 || xb.Length != yb.Length) return false;
            var source = new BoundSourceQuery(state);
            var xp = f.Blocks.SelectMany(block => block.Statements.Select((statement, i) => (statement, Point: new Point(block.Identity, i))))
                .Single(pair => pair.statement == xcall).Point;
            var yp = f.Blocks.SelectMany(block => block.Statements.Select((statement, i) => (statement, Point: new Point(block.Identity, i))))
                .Single(pair => pair.statement == ycall).Point;
            IEnumerable<BoundValue> Arguments(BoundCall binding) => binding.Signature.Managed is not null
                && binding.Signature.Entry?.Method is { } method && !GenericWitness.IsGeneric(method.Method)
                ? (binding.This is { } receiver ? new[] { receiver } : []).Concat(binding.Parameters) : binding.Arguments;
            // 普通托管调用的身份已确定 MethodInfo；共享泛型仍须复核上下文实参。
            return xb.Zip(yb).All(pair => Arguments(pair.First).Count() == Arguments(pair.Second).Count()
                && Arguments(pair.First).Zip(Arguments(pair.Second)).All(arguments =>
                {
                    var leftValue = c.Get(source, new(arguments.First.Source, xp));
                    var rightValue = c.Get(source, new(arguments.Second.Source, yp));
                    return leftValue.IsSuccess && rightValue.IsSuccess && Same(leftValue.Value, rightValue.Value);
                }));
        }
        var omitted = new HashSet<Statement>();
        var live = new StructureLiveness(f, SemanticEndUses);
        var discarded = blocks.Keys.Except(retained.Keys).ToImmutableHashSet();
        var frontier = new EventFrontierQuery((_, point) => Cpp2CS.Kernel.Queries.Outcome<bool>.Success(
            point.Before == blocks[point.Block].Statements.Length ? blocks[point.Block].End is not Jump
                : !privateStatement(blocks[point.Block].Statements[point.Before])));
        foreach (var exit in exits)
        {
            var normal = blocks[exit];
            var prefix = new List<Statement>(); var next = new Point(exit, 0);
            for (int i = 0; i < operations.Length; i++)
            {
                var found = c.Get(frontier, new(next));
                if (!found.IsSuccess || found.Value.HasCycle || found.Value.ReachesExit || found.Value.Stops.Count != 1) return null;
                var point = found.Value.Stops.Single();
                if (point.Before == blocks[point.Block].Statements.Length || !Dominates(exit, point.Block)) return null;
                prefix.Add(blocks[point.Block].Statements[point.Before]); next = point with { Before = point.Before + 1 };
            }
            if (projectedIndex.Value.Predecessors[normal.Identity].Any(point => !protectedBlocks.Contains(point.Block))) return null;
            if (normal.Handler is not null || !operations.Zip(prefix).All(pair => SameStatement(pair.First, pair.Second))
                || prefix.OfType<Call>().SelectMany(call => call.Results).Any(result => live.Used(result.Value))) return null;
            omitted.UnionWith(prefix);
        }
        return new(clause.Entry, body, chain[^1].Identity, exits[0], discarded, [], ImmutableDictionary<Term, Term>.Empty)
        { Omitted = omitted.Append(last).ToImmutableHashSet(), PropagatesTo = unwind[last.Identity], Branches = branches.ToImmutable(), Unreachable = discarded };
    }
}
