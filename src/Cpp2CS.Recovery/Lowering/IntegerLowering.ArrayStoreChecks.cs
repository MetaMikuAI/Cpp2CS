using Cpp2CS.Kernel.Flow;
using Cpp2CS.Model;
using Cpp2CS.Recovery.Naming;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Kernel.State;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;
using Cpp2CS.Recovery.Binding;
using Cpp2CS.Recovery.Checks;
using Cpp2CS.Recovery.Locations;
using Cpp2CS.Runtime;

namespace Cpp2CS.Recovery.Lowering;

public sealed partial class IntegerLowering
{
    private readonly Dictionary<CallIdentity, (Term Array, Term Value, Point Point)> arrayStoreChecks = [];

    private void PrepareArrayStoreCheck(Call call, ClassifiedCall classified, Point point)
    {
        if (classified.Inputs?.GetValueOrDefault("array")?.Source is not TermSource array
            || classified.Inputs?.GetValueOrDefault("value")?.Source is not TermSource value)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数组存入检查的数组或值没有绑定", code: "lowering.ArrayStoreCheck"); return; }
        arrayStoreChecks.Add(call.Identity, (array.Term, value.Term, point));
        PairArrayStoreCheck(call.Identity);
    }

    private void PairArrayStoreCheck(CallIdentity id)
    {
        var check = arrayStoreChecks[id];
        var block = function.Blocks.Single(b => b.Identity == check.Point.Block);
        position = block.Statements[check.Point.Before].Trace?.NativeAddress ?? block.Trace?.NativeAddress ?? 0;
        if (locations is null || valueNames is null || calls is null)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数组存入检查缺少位置及定值查询", code: "lowering.ArrayStoreCheck"); return; }
        Reason? pairingWhy = null;
        bool Same(Term a, Term b) => valueNames.SameValue(context, a, b) is { IsSuccess: true, Value: true };
        bool Store(Point point)
        {
            var b = function.Blocks.Single(b => b.Identity == point.Block);
            if (point.Before >= b.Statements.Length || b.Statements[point.Before] is not MemoryWrite write) return false;
            if (write.Width != types.PointerSize * 8 || !Same(write.Value, check.Value))
            { pairingWhy ??= new("lowering.ArrayStoreCheck.Value", "写入宽度或 value 与检查不相同。"); return false; }
            var located = context.Get(locations, new(write.Address, write.Width));
            bool matched = located.IsSuccess && located.Value.Views.Count(v => v.Kind == ManagedLocationKind.ArrayElement
                && v.Path.IsEmpty && v.Offset == 0 && v.Width == write.Width && ManagedTypes.IsReferenceType(v.Type)
                && Same(v.Root, check.Array)) == 1;
            if (!matched) pairingWhy ??= new("lowering.ArrayStoreCheck.Location", "写入位置没有同一数组的唯一完整引用元素视图。", located.Why ?? located.Value?.Why);
            return matched;
        }
        Outcome<bool> Stop(QueryContext c, Point point)
        {
            var b = function.Blocks.Single(b => b.Identity == point.Block);
            if (point.Before == b.Statements.Length) return Outcome<bool>.Success(b.End is Branch);
            var statement = b.Statements[point.Before];
            if (statement is Call call)
            {
                var named = c.Get(calls, call.Identity);
                return named.IsSuccess ? Outcome<bool>.Success(named.Value.Operation?.Observation != RuntimeObservation.Unobservable) : named.Propagate<bool>();
            }
            if (statement is MemoryRead read)
            {
                if (read.Acquire) return Outcome<bool>.Success(true);
                if (PrivateAccess(read)) return Outcome<bool>.Success(false);
                var located = c.Get(locations, new(read.Address, read.Width));
                return located.IsSuccess ? Outcome<bool>.Success(!located.Value.Views.Any(v => v.Kind == ManagedLocationKind.ArrayLength && Same(v.Root, check.Array))) : located.Propagate<bool>();
            }
            return Outcome<bool>.Success(statement is not MemoryWrite write || write.Release || !PrivateAccess(write));
        }
        var frontier = context.Get(new EventFrontierQuery(Stop), new(new(check.Point.Block, check.Point.Before + 1)));
        bool valid = frontier.IsSuccess && !frontier.Value.ReachesExit && !frontier.Value.HasCycle && frontier.Value.Stops.Count != 0;
        var checks = new CheckQueries(state, calls, locations);
        if (valid)
        foreach (var point in frontier.Value.Stops)
        {
            if (Store(point)) continue;
            var b = function.Blocks.Single(b => b.Identity == point.Block);
            // 存入自身的越界检查沿用共享检查查询的事件前沿和同一数组/下标证明。
            bool bounds = point.Before == b.Statements.Length && b.End is Branch branch
                && new[] { branch.True, branch.False }.Any(target =>
                {
                    var answer = context.Get(checks.Checks, new(b.Identity, target));
                    if (answer is not { IsSuccess: true, Value: { Exception: "System.IndexOutOfRangeException" } guard }) return false;
                    bool matched = guard.CanAbsorb && guard.Subject.Array is { } array && Same(array, check.Array)
                        && guard.Accesses.Count != 0 && guard.Accesses.All(Store);
                    if (!matched) pairingWhy ??= new("lowering.ArrayStoreCheck.Bounds", "越界检查没有由同一次写入吸收的凭据。", guard.ExplicitReason);
                    return matched;
                });
            if (!bounds) { pairingWhy ??= new("lowering.ArrayStoreCheck.Event", "存入之前遇到其他事件、访问或未证明的分支。"); valid = false; break; }
        }
        if (!valid)
        { Fail<object>(LoweringFailureKind.RuntimeCall, "数组存入检查之后没有无间隔事件的同数组、同值引用元素存入", frontier.Why ?? pairingWhy, "lowering.ArrayStoreCheck"); return; }
    }
}
