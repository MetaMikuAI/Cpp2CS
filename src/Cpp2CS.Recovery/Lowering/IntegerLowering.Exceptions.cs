using Cpp2CS.Managed;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Exceptions;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Kernel.State;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Recovery.Dispatch;
using Cpp2CS.Recovery.Locations;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private ExceptionPlan? exceptions;
    private FinallyPlan[] finallyRegions = [];
    private readonly Dictionary<Term, Term> exceptionAliases = [];
    private readonly Dictionary<(BlockIdentity From, BlockIdentity To), BlockIdentity> exceptionTargets = [];
    private BlockIdentity? currentNativeBlock;
    private readonly Dictionary<ExceptionClausePlan, LocalValue> caughtLocals = [];
    private readonly Dictionary<CallIdentity, List<ManagedCopy>> arrivals = [];
    private readonly Dictionary<ManagedStatement, CallIdentity> exceptionCallStatements = new(ReferenceEqualityComparer.Instance);

    private sealed record ExceptionView(QueryContext Context, ValueNamingQuery Names, ManagedLocationQuery Locations, DispatchQuery Dispatch);
    private ExceptionView? ordinaryView;
    private readonly Dictionary<BlockIdentity, ExceptionView> exceptionViews = [];

    private void SelectExceptionView(BlockIdentity block)
    {
        currentNativeBlock = block;
        if (exceptions is null || ordinaryView is null) return;
        var view = exceptionViews.GetValueOrDefault(block) ?? ordinaryView;
        context = view.Context; valueNames = view.Names; locations = view.Locations; dispatch = view.Dispatch;
        values.Clear();
    }

    private void PrepareExceptions()
    {
        if (!function.Blocks.Any(b => b.Handler is not null)) return;
        if (calls is null || valueNames is null || spec is null)
        { Fail<object>(LoweringFailureKind.Exception, "异常恢复缺少目录、命名或布局", code: "lowering.Exception.State"); return; }
        var answer = context.Get(new ExceptionRegionQuery(state, calls, valueNames, spec, types.Object, nestedExceptions), 0);
        if (!answer.IsSuccess)
        { Fail<object>(LoweringFailureKind.Exception, answer.Why!.Message, answer.Why.Cause, answer.Why.Code); return; }
        exceptions = answer.Value;
        finallyRegions = exceptions.Regions.SelectMany(r => r.Clauses).Where(clause => clause.Finally is not null).Select(clause => clause.Finally!).ToArray();
        foreach (var plan in finallyRegions)
        {
            foreach (var (value, alias) in plan.Values) exceptionAliases.Add(value, alias);
            foreach (var from in plan.Arrivals) exceptionTargets.Add((from, plan.Entry), plan.LeaveTargets.GetValueOrDefault(from) ?? plan.Continuation);
        }
        foreach (var clause in exceptions.Regions.SelectMany(r => r.Clauses).Where(clause => clause.Finally is null))
            caughtLocals.Add(clause, new(new(nextLocal++), clause.Type, types.PointerSize * 8));
        PrepareExceptionViews();
    }

    private void PrepareExceptionViews()
    {
        if (exceptions is null) return;
        ordinaryView = new(context, valueNames!, locations!, dispatch!);
        exceptionViews.Clear();
        var views = new List<(ExceptionClausePlan[] Clauses, ExceptionView View)>();
        foreach (var block in function.Blocks)
        {
            var clauses = exceptions.Regions.SelectMany(r => r.Clauses).Where(clause => clause.Finally is null && clause.Body.Contains(block.Identity)).ToArray();
            if (clauses.Length == 0) continue;
            var existing = views.FirstOrDefault(v => v.Clauses.SequenceEqual(clauses)).View;
            if (existing is not null) { exceptionViews.Add(block.Identity, existing); continue; }
            var refined = clauses.ToDictionary(clause => clause.Source, clause => clause.Type);
            var naming = ordinaryView.Names.WithCaughtTypes(refined);
            var located = new ManagedLocationQuery(state, naming, types.Layouts, spec!, frameObjects);
            var view = new ExceptionView(located.CreateContext(function), naming, located,
                new(state, calls!, naming, located, binder, spec!, types.Layouts as Cpp2CS.Recovery.Binding.GenericWitness));
            exceptionViews.Add(block.Identity, view); views.Add((clauses, view));
        }
    }

    private ManagedValue? CaughtValue(Term term)
    {
        if (exceptions is null || valueNames is null || currentNativeBlock is null) return null;
        if (context.Get(valueNames, term) is not { IsSuccess: true, Value.Name: CaughtExceptionName caught }) return null;
        var clause = caughtLocals.Keys.SingleOrDefault(p => p.Source == caught.Handler && p.Body.Contains(currentNativeBlock));
        return clause is null ? Fail<ManagedValue>(LoweringFailureKind.Exception,
            "捕获异常在所属 catch 子句之外使用", code: "lowering.Exception.State") : caughtLocals[clause];
    }

    /// <summary>值（沿合流的各输入）里有捕获的异常，而当前块不在它的处理体内。</summary>
    private bool StoredCaughtException(Term term)
    {
        if (exceptions is null || valueNames is null || currentNativeBlock is not { } here) return false;
        var seen = new HashSet<Term>(); var work = new Stack<Term>(); work.Push(term);
        while (work.TryPop(out var current))
        {
            if (!seen.Add(current)) continue;
            if (context.Get(valueNames, current) is { IsSuccess: true, Value.Name: CaughtExceptionName caught }
                && !caughtLocals.Keys.Any(clause => clause.Source == caught.Handler && clause.Body.Contains(here))) return true;
            if (current.Identity is ResultAtom { Definition: MergeIdentity id } && definitions.TryGetValue(id, out var merge))
                foreach (var input in merge.Merge.Inputs) work.Push(input.Value);
        }
        return false;
    }

    private ManagedBody ExceptionBody(IReadOnlyList<ManagedBlock> blocks)
    {
        var body = new ManagedBody(method, blocks);
        if (exceptions is null) return body;
        var order = exceptions.Order.Select(id => labels[id]).ToArray();
        if (extraBlocks.Count != 0)
        {
            Fail<object>(LoweringFailureKind.Exception, "异常区域中的跳转表扩展尚未建立区域归属", code: "lowering.Exception.Region");
            return body;
        }
        var byAddress = blocks.ToDictionary(block => block.Address);
        return body with
        {
            Blocks = order.Select(id =>
            {
                var block = byAddress[id];
                var plan = finallyRegions.FirstOrDefault(plan => labels[plan.Completion] == id);
                if (plan is null) return block;
                var edge = ((ManagedJump)block.Statements[^1]).Edge;
                var temps = edge.Copies.Select(copy => new LocalValue(new(nextLocal++), copy.Target.Type, copy.Target.Width)).ToArray();
                return block with { Statements = block.Statements.SkipLast(1)
                    .Concat(edge.Copies.Select((copy, i) => (ManagedStatement)new ManagedAssignment(0, temps[i], copy.Value)))
                    .Concat(edge.Copies.Select((copy, i) => (ManagedStatement)new ManagedAssignment(0, copy.Target, temps[i])))
                    .Append(new ManagedEndFault(0)).ToArray() };
            }).ToArray(),
            Regions = exceptions.Regions.SelectMany(r => r.Clauses.Select(clause => new ManagedRegion(
                exceptions.Order.Where(r.Try.Contains).Select(id => labels[id]).ToArray(), labels[clause.Entry],
                exceptions.Order.Where(clause.Body.Contains).Select(id => labels[id]).ToArray(), clause.Finally is null ? caughtLocals[clause] : null, clause.Finally is null ? ManagedRegionKind.Catch : ManagedRegionKind.Finally)
                { CatchType = clause.Finally is null ? clause.Type : null })).ToArray(),
        };
    }

    private Term? ExceptionAlias(Term value) => exceptionAliases.GetValueOrDefault(value);

    private BlockIdentity ExceptionTarget(BlockIdentity from, BlockIdentity target) =>
        exceptionTargets.GetValueOrDefault((from, target)) ?? target;

    private bool ExceptionCopy(BlockIdentity from, BlockIdentity to, LocalValue local, ManagedValue value)
    {
        if (exceptions is null || function.Blocks.Single(b => b.Identity == to).Handler is null) return false;
        var targets = function.Blocks.Single(b => b.Identity == from).Statements.OfType<Call>().Where(c => c.Unwind == to).ToArray();
        if (targets.Length != 1)
        { Fail<object>(LoweringFailureKind.Exception, "展开合流的前驱没有唯一调用点", code: "lowering.Exception.State"); return true; }
        var call = targets[0];
        if (!arrivals.TryGetValue(call.Identity, out var list)) arrivals.Add(call.Identity, list = []);
        list.Add(new(local, value));
        return true;
    }
}
