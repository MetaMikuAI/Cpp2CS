using Cpp2CS.Kernel.Flow;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Checks;

internal sealed record CheckedUnboxFusion(Call Check, Term Object, Term Class, Term Result, BlockIdentity? Test, BlockIdentity? Pass);

/// <summary>非空对象上的类型判断，只有失败出口恰为同对象转换失败且结果不外泄时，才能与随后的拆箱合并。</summary>
internal sealed class CheckedUnboxFusionQuery(StateQueries state, CallNamingQuery calls, ValueNamingQuery names, ManagedLocationQuery locations)
    : Query<CallIdentity, CheckedUnboxFusion?>
{
    private readonly UncheckedUnboxQuery unboxes = new(state, calls, names);
    private readonly CheckQueries checks = new(state, calls, locations);
    private readonly PathFactQuery paths = new(state);
    private readonly FlowQueries flow = new();
    public override Outcome<CheckedUnboxFusion?> Compute(QueryContext c, CallIdentity key)
    {
        Outcome<CheckedUnboxFusion?> None() => Outcome<CheckedUnboxFusion?>.Success(null);
        var proof = c.Get(unboxes, key);
        if (!proof.IsSuccess || proof.Value.TypeCheck is not { } checkId) return None();
        var origin = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == checkId));
        var check = origin.Statements.OfType<Call>().Single(x => x.Identity == checkId);
        var target = c.Snapshot.Blocks.Single(b => b.Statements.OfType<Call>().Any(x => x.Identity == key));
        var unbox = target.Statements.OfType<Call>().Single(x => x.Identity == key);
        var source = c.Get(calls, checkId);
        if (check.Unwind is not null || unbox.Unwind is not null || !source.IsSuccess
            || source.Value.Inputs?.GetValueOrDefault("object")?.Source is not TermSource obj
            || source.Value.Inputs?.GetValueOrDefault("class")?.Source is not TermSource klass
            || source.Value.Result?.Source is not TermSource returned) return None();
        var start = new Point(origin.Identity, origin.Statements.IndexOf(check));
        if (!unboxes.NonNull(c, obj.Term, start)) return None();
        var end = new Point(target.Identity, target.Statements.IndexOf(unbox));
        if (new Point(start.Block, start.Before + 1) != end
            && c.Get(flow.PointDominates, new(new(start.Block, start.Before + 1), end)) is not { IsSuccess: true, Value: true }) return None();
        BlockIdentity? test = null, pass = null;
        bool Uses(Term value) => SnapshotRewrite.Dependencies([value]).Contains(returned.Term);
        if (source.Value.Operation?.Il.Name == "IsInst")
        {
            var nonnull = c.Snapshot.Terms.Apply(new CoreOperator(CoreOperation.NotEqual), 1, returned.Term, c.Snapshot.Terms.Constant(0, returned.Term.Width));
            foreach (var block in c.Snapshot.Blocks.Where(b => b.End is Branch))
            {
                var branch = (Branch)block.End;
                var yes = new FlowEdge(block.Identity, branch.True); var no = new FlowEdge(block.Identity, branch.False);
                var positive = c.Get(paths, new(default, nonnull, yes)); var negative = c.Get(paths, new(default, nonnull, no));
                if (!positive.IsSuccess || !negative.IsSuccess || positive.Value == PathTruth.Unknown || negative.Value == PathTruth.Unknown || positive.Value == negative.Value) continue;
                var failed = positive.Value == PathTruth.True ? branch.False : branch.True;
                var throwing = c.Get(checks.ThrowOnly, failed);
                if (!throwing.IsSuccess || throwing.Value?.Exception != "System.InvalidCastException") continue;
                bool matches = true;
                foreach (var point in throwing.Value.Throws)
                {
                    if (CheckQueries.Statement(c, point) is not Call call || c.Get(calls, call.Identity) is not { IsSuccess: true } named
                        || named.Value.Inputs?.GetValueOrDefault("object")?.Source is not TermSource thrownObject
                        || named.Value.Inputs?.GetValueOrDefault("class")?.Source is not TermSource thrownClass
                        || names.SameValue(c, thrownObject.Term, obj.Term) is not { IsSuccess: true, Value: true }
                        || names.SameValue(c, thrownClass.Term, klass.Term) is not { IsSuccess: true, Value: true }) matches = false;
                }
                if (!matches || test is not null) return None();
                test = block.Identity; pass = positive.Value == PathTruth.True ? branch.True : branch.False;
            }
            if (test is null) return None();
        }
        foreach (var block in c.Snapshot.Blocks)
        {
            if (block.Merges.SelectMany(m => m.Inputs.Select(i => i.Value)).Any(Uses)
                || block.Identity != test && SnapshotRewrite.Uses(block.End).Any(Uses)) return None();
            foreach (var statement in block.Statements)
                if (statement != unbox && SnapshotRewrite.Uses(statement).Any(Uses)) return None();
        }
        Outcome<bool> Stop(QueryContext context, Point point, bool atTest)
        {
            var block = context.Snapshot.Blocks.Single(b => b.Identity == point.Block);
            if (atTest && test == block.Identity && point.Before == block.Statements.Length) return Outcome<bool>.Success(true);
            if (point.Before == block.Statements.Length) return Outcome<bool>.Success(false);
            var statement = block.Statements[point.Before];
            if (statement is MemoryRead read)
            {
                var address = context.Get(state.Resolve, read.Address);
                var location = address.IsSuccess ? context.Get(state.Locations, new(address.Value, read.Width)) : default;
                var fixedValue = names.FixedValue(context, read.Result);
                return Outcome<bool>.Success(!(location.IsSuccess && location.Value.Region == Region.Frame)
                    && fixedValue is not { IsSuccess: true, Value: EntityName or FieldName or ArrayElementName });
            }
            return Outcome<bool>.Success(true);
        }
        var frontier = new EventFrontierQuery((context, point) => Stop(context, point, true));
        bool Only(FrontierStart from, Point wanted)
        {
            var result = c.Get(frontier, from);
            return result.IsSuccess && !result.Value.HasCycle && !result.Value.ReachesExit && result.Value.Stops.Count == 1 && result.Value.Stops.Contains(wanted);
        }
        if (test is { } testBlock)
        {
            if (!Only(new(new(start.Block, start.Before + 1)), new(testBlock, c.Snapshot.Blocks.Single(b => b.Identity == testBlock).Statements.Length))) return None();
            // 已越过类型分支，不把终结本身再作为停点。
            var targetFrontier = new EventFrontierQuery((context, point) => Stop(context, point, false));
            var next = c.Get(targetFrontier, FrontierStart.FromEdge(new(testBlock, pass!)));
            if (!next.IsSuccess || next.Value.HasCycle || next.Value.ReachesExit || next.Value.Stops.Count != 1 || !next.Value.Stops.Contains(end)) return None();
        }
        else if (!Only(new(new(start.Block, start.Before + 1)), end)) return None();
        return Outcome<CheckedUnboxFusion?>.Success(new(check, obj.Term, klass.Term, returned.Term, test, pass));
    }
}
