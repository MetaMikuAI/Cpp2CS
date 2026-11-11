using System.Collections.Immutable;
using Cpp2CS.Kernel.Queries;
using Cpp2CS.Native;
using Cpp2CS.Native.Terms;

namespace Cpp2CS.Kernel.State;

public sealed record CallerUse(Point Point, string Use, CallerValue Caller, Reason Reason);
public sealed class CallerUsesQuery(StateQueries q) : Query<int, ImmutableArray<CallerUse>>
{
    public override Outcome<ImmutableArray<CallerUse>> Compute(QueryContext c, int key)
    {
        var uses = ImmutableArray.CreateBuilder<CallerUse>();
        var sinks = new List<(Point Point, string Use, Term Value)>();
        foreach (var b in c.Snapshot.Blocks)
        {
            for (int i = 0; i < b.Statements.Length; i++)
            {
                var p = new Point(b.Identity, i);
                switch (b.Statements[i])
                {
                    case Call call:
                        foreach (var a in call.Arguments) sinks.Add((p, "调用实参", a.Value));
                        if (call.Target is ComputedTarget target) sinks.Add((p, "调用目标", target.Value));
                        break;
                    case MemoryWrite w:
                        var address = c.Get(q.Resolve, w.Address); if (!address.IsSuccess) return address.Propagate<ImmutableArray<CallerUse>>();
                        var l = c.Get(q.Locations, new(address.Value, w.Width)); if (!l.IsSuccess) return l.Propagate<ImmutableArray<CallerUse>>();
                        if (l.Value.Region != Region.Frame) sinks.Add((p, "非帧写入", w.Value));
                        break;
                    case TrapWhen trap: sinks.Add((p, "陷阱条件", trap.Condition)); break;
                }
            }
            var end = new Point(b.Identity, b.Statements.Length);
            switch (b.End)
            {
                case Return r: foreach (var v in r.Results) sinks.Add((end, "返回值", v.Value)); break;
                case Branch branch: sinks.Add((end, "分支条件", branch.Condition)); break;
                case JumpTable table: sinks.Add((end, "分支选择", table.Selector)); break;
                case ResumeUnwind unwind: sinks.Add((end, "继续展开", unwind.Exception)); break;
            }
        }
        foreach (var sink in sinks)
        {
            var pending = new Stack<Term>(); pending.Push(sink.Value); var seen = new HashSet<Term>();
            var callers = new HashSet<CallerValue>();
            while (pending.TryPop(out var raw))
            {
                if (!seen.Add(raw)) continue;
                var resolved = c.Get(q.Resolve, raw); if (!resolved.IsSuccess) return resolved.Propagate<ImmutableArray<CallerUse>>();
                var term = resolved.Value;
                if (term.Identity is CallerValue caller && callers.Add(caller))
                    uses.Add(new(sink.Point, sink.Use, caller, new("state.caller-use", "调用方的值进入可观察的使用。")));
                foreach (var child in term.Operands) pending.Push(child);
                if (term.Identity is MemoryMerge merge)
                {
                    var inputs = c.Get(q.MergeInputs, merge); if (!inputs.IsSuccess) return inputs.Propagate<ImmutableArray<CallerUse>>();
                    foreach (var input in inputs.Value) pending.Push(input.Value);
                }
                if (term.Identity is ResultAtom { Definition: MergeIdentity id })
                    foreach (var input in c.Snapshot.Blocks.SelectMany(b => b.Merges).Single(m => m.Identity == id).Inputs) pending.Push(input.Value);
            }
        }
        return Outcome<ImmutableArray<CallerUse>>.Success(uses.ToImmutable());
    }
}
